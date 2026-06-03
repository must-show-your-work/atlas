"""Flask app that backs `atlas serve`.

Two responsibilities:
  - Serve the static viewer (`scripts/*.html`, `vendor/*`, `blueprint/*.json`)
    using the same project-then-atlas layered resolution as the old
    stdlib implementation.
  - Host a small JSON API (`/api/flags`, `/api/notes`) backed by
    SQLite. This is the writable annotation layer the viewer talks to
    when a reviewer flags a section or jots a note. Lives at
    `<project_root>/blueprint/atlas.sqlite` so `just graph` blowing
    away `graph.kuzu` doesn't touch user annotations.

SQLite was chosen over going straight to Kuzu so the regen path stays
purely read-only on the graph DB. The eventual v2 plan is to fold these
back into Kuzu as additional node/edge tables — at which point the API
shape here should stay stable.
"""

from __future__ import annotations

import datetime as _dt
import sqlite3
import sys
from pathlib import Path
from urllib.parse import unquote

from flask import Flask, abort, g, jsonify, request, send_file


VALID_SECTIONS = {
    "statement", "figure", "source", "commentary", "references", "book-proof"
}


def _utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds")


def _connect(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(str(db_path))
    conn.row_factory = sqlite3.Row
    # WAL is friendlier under concurrent reads (viewer GET while a POST
    # commits) and survives crash-on-write without DB corruption.
    conn.execute("PRAGMA journal_mode = WAL")
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def _init_schema(db_path: Path) -> None:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    with _connect(db_path) as conn:
        conn.executescript("""
            CREATE TABLE IF NOT EXISTS flags (
              decl_id    TEXT NOT NULL,
              section    TEXT NOT NULL,
              created_at TEXT NOT NULL,
              PRIMARY KEY (decl_id, section)
            );
            CREATE INDEX IF NOT EXISTS flags_by_decl ON flags(decl_id);

            CREATE TABLE IF NOT EXISTS notes (
              id         INTEGER PRIMARY KEY AUTOINCREMENT,
              decl_id    TEXT NOT NULL,
              section    TEXT,
              body       TEXT NOT NULL,
              created_at TEXT NOT NULL,
              updated_at TEXT NOT NULL
            );
            CREATE INDEX IF NOT EXISTS notes_by_decl ON notes(decl_id);

            CREATE TABLE IF NOT EXISTS line_flags (
              decl_id    TEXT NOT NULL,
              line       INTEGER NOT NULL,
              created_at TEXT NOT NULL,
              PRIMARY KEY (decl_id, line)
            );
            CREATE INDEX IF NOT EXISTS line_flags_by_decl ON line_flags(decl_id);
        """)


def create_app(atlas_root: Path, project_root: Path) -> Flask:
    app = Flask(__name__, static_folder=None)
    db_path = project_root / "blueprint" / "atlas.sqlite"
    _init_schema(db_path)
    app.config["DB_PATH"] = db_path
    app.config["ATLAS_ROOT"] = atlas_root
    app.config["PROJECT_ROOT"] = project_root

    @app.before_request
    def _open_db():
        g.db = _connect(app.config["DB_PATH"])

    @app.teardown_request
    def _close_db(_exc):
        db = g.pop("db", None)
        if db is not None:
            db.close()

    @app.after_request
    def _no_cache(resp):
        # Same reasoning as the old stdlib handler: the dev workflow
        # edits these files between requests and stale browser caches
        # masquerade as bugs. JSON API responses get the same treatment
        # so the viewer always sees fresh annotation state.
        resp.headers["Cache-Control"] = "no-store, must-revalidate"
        resp.headers["Pragma"] = "no-cache"
        resp.headers["Expires"] = "0"
        return resp

    # -------- API: flags --------

    @app.get("/api/flags")
    def list_flags():
        rows = g.db.execute(
            "SELECT decl_id, section, created_at FROM flags"
        ).fetchall()
        out: dict[str, dict[str, str]] = {}
        for r in rows:
            out.setdefault(r["decl_id"], {})[r["section"]] = r["created_at"]
        return jsonify(out)

    @app.post("/api/flags")
    def add_flag():
        data = request.get_json(silent=True) or {}
        decl_id = (data.get("decl_id") or "").strip()
        section = (data.get("section") or "").strip()
        if not decl_id or section not in VALID_SECTIONS:
            abort(400, description="missing/invalid decl_id or section")
        g.db.execute(
            "INSERT OR IGNORE INTO flags(decl_id, section, created_at) "
            "VALUES (?, ?, ?)",
            (decl_id, section, _utc_now()),
        )
        g.db.commit()
        return jsonify({"ok": True})

    @app.delete("/api/flags/<path:decl_id>/<section>")
    def remove_flag(decl_id: str, section: str):
        decl_id = unquote(decl_id)
        if section not in VALID_SECTIONS:
            abort(400, description="invalid section")
        g.db.execute(
            "DELETE FROM flags WHERE decl_id = ? AND section = ?",
            (decl_id, section),
        )
        g.db.commit()
        return jsonify({"ok": True})

    # -------- API: line flags --------
    # Flags scoped to a single source line of a decl. Used by the
    # source-pane click-to-flag UI: shift-click expands to a range
    # which the client POSTs as individual lines.

    @app.get("/api/line-flags")
    def list_line_flags():
        decl = request.args.get("decl")
        if not decl:
            abort(400, description="missing decl param")
        rows = g.db.execute(
            "SELECT line, created_at FROM line_flags WHERE decl_id = ? ORDER BY line",
            (decl,),
        ).fetchall()
        return jsonify({str(r["line"]): r["created_at"] for r in rows})

    @app.post("/api/line-flags")
    def add_line_flag():
        data = request.get_json(silent=True) or {}
        decl_id = (data.get("decl_id") or "").strip()
        line = data.get("line")
        if not decl_id or not isinstance(line, int) or line < 0:
            abort(400, description="missing/invalid decl_id or line")
        g.db.execute(
            "INSERT OR IGNORE INTO line_flags(decl_id, line, created_at) "
            "VALUES (?, ?, ?)",
            (decl_id, line, _utc_now()),
        )
        g.db.commit()
        return jsonify({"ok": True})

    @app.delete("/api/line-flags/<path:decl_id>/<int:line>")
    def remove_line_flag(decl_id: str, line: int):
        decl_id = unquote(decl_id)
        g.db.execute(
            "DELETE FROM line_flags WHERE decl_id = ? AND line = ?",
            (decl_id, line),
        )
        g.db.commit()
        return jsonify({"ok": True})

    # -------- API: notes --------

    @app.get("/api/notes")
    def list_notes():
        decl = request.args.get("decl")
        if decl:
            rows = g.db.execute(
                "SELECT * FROM notes WHERE decl_id = ? ORDER BY created_at",
                (decl,),
            ).fetchall()
        else:
            rows = g.db.execute(
                "SELECT * FROM notes ORDER BY decl_id, created_at"
            ).fetchall()
        return jsonify([dict(r) for r in rows])

    @app.post("/api/notes")
    def add_note():
        data = request.get_json(silent=True) or {}
        decl_id = (data.get("decl_id") or "").strip()
        section = data.get("section")
        body = (data.get("body") or "").strip()
        if not decl_id or not body:
            abort(400, description="missing decl_id or body")
        if section is not None and section not in VALID_SECTIONS:
            abort(400, description="invalid section")
        now = _utc_now()
        cur = g.db.execute(
            "INSERT INTO notes(decl_id, section, body, created_at, updated_at) "
            "VALUES (?, ?, ?, ?, ?)",
            (decl_id, section, body, now, now),
        )
        g.db.commit()
        return jsonify({"ok": True, "id": cur.lastrowid})

    @app.put("/api/notes/<int:note_id>")
    def update_note(note_id: int):
        data = request.get_json(silent=True) or {}
        body = (data.get("body") or "").strip()
        if not body:
            abort(400, description="missing body")
        g.db.execute(
            "UPDATE notes SET body = ?, updated_at = ? WHERE id = ?",
            (body, _utc_now(), note_id),
        )
        g.db.commit()
        return jsonify({"ok": True})

    @app.delete("/api/notes/<int:note_id>")
    def delete_note(note_id: int):
        g.db.execute("DELETE FROM notes WHERE id = ?", (note_id,))
        g.db.commit()
        return jsonify({"ok": True})

    # -------- Static viewer (layered) --------
    # Routes for known top-level dirs we serve, plus an index redirect.
    # We don't use Flask's static_folder because the layered resolution
    # (project then atlas-package) needs custom logic.

    def _resolve(path: str) -> Path | None:
        relpath = unquote(path.split("?", 1)[0].split("#", 1)[0]).lstrip("/")
        if ".." in relpath.split("/"):
            return None
        for root in (app.config["PROJECT_ROOT"], app.config["ATLAS_ROOT"]):
            cand = Path(root) / relpath
            if cand.is_file():
                return cand
            if cand.is_dir():
                idx = cand / "index.html"
                if idx.is_file():
                    return idx
        return None

    @app.get("/")
    def index():
        # No project index; point at the TOC view.
        return jsonify({
            "ok": True,
            "graph_view": "/scripts/graph.html",
            "toc_view":   "/scripts/toc.html",
        })

    @app.get("/<path:path>")
    def static_layered(path: str):
        resolved = _resolve(path)
        if resolved is None:
            abort(404)
        # Flask handles mimetype detection from the extension.
        return send_file(resolved)

    return app


def serve(atlas_root: Path, project_root: Path, host: str, port: int) -> int:
    app = create_app(atlas_root, project_root)
    db = app.config["DB_PATH"]
    print(f"[atlas serve] atlas package:    {atlas_root}", file=sys.stderr)
    print(f"[atlas serve] project root:     {project_root}", file=sys.stderr)
    print(f"[atlas serve] annotation db:    {db}", file=sys.stderr)
    print(f"[atlas serve] listening on:     http://{host}:{port}/", file=sys.stderr)
    print(f"[atlas serve]   graph view:     http://{host}:{port}/scripts/graph.html", file=sys.stderr)
    print(f"[atlas serve]   toc view:       http://{host}:{port}/scripts/toc.html", file=sys.stderr)
    if host == "0.0.0.0":
        print(f"[atlas serve] open externally:   sudo nixos-firewall-tool open tcp {port}",
              file=sys.stderr)
    print("[atlas serve] Ctrl-C to stop", file=sys.stderr)
    try:
        # threaded=True so the viewer's parallel asset fetches don't
        # serialize behind each other. Flask's dev server is fine for
        # this single-user workflow; we're not chasing prod throughput.
        app.run(host=host, port=port, threaded=True, use_reloader=False)
    except OSError as e:
        print(f"[atlas serve] failed to bind {host}:{port}: {e}", file=sys.stderr)
        return 1
    return 0
