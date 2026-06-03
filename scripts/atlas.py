#!/usr/bin/env python3
"""atlas CLI.

Single entry point for the Atlas tooling: dump, import, serve, query,
inspect, check, db ops. Each subcommand is a thin orchestration layer
around the Lake exe / Python helper / kuzu commands that already exist
in scripts/.

Designed to be invoked either as:
  - `./atlas <verb> [args...]`           (via bin/atlas symlink in cwd)
  - `lake exe atlas <verb> [args...]`    (if/when the Lean wrapper lands)
  - `python3 scripts/atlas.py <verb>`    (direct, in the atlas repo)

CWD is treated as the consumer-project root: `atlas dump` writes
dumps under `<cwd>/blueprint/`, `atlas serve` serves files relative
to cwd, etc. The atlas-repo path is resolved separately (from this
script's location) for finding internal helpers.

This file is a SKELETON — most subcommands are stubbed. As they're
implemented, each will inherit reasonable defaults from environment
variables (`ATLAS_TARGET_MODULE`, `ATLAS_BLUEPRINT_DIR`, etc.).
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


# ---- Paths -----------------------------------------------------------------

# Atlas-package root, resolved from this script's location.
ATLAS_ROOT = Path(__file__).resolve().parent.parent
# Consumer-project root = cwd at invocation. Configurable via env.
PROJECT_ROOT = Path(os.environ.get("ATLAS_PROJECT_ROOT", os.getcwd()))
# Default blueprint dir under the consumer project.
BLUEPRINT_DIR = Path(os.environ.get(
    "ATLAS_BLUEPRINT_DIR", str(PROJECT_ROOT / "blueprint")))
# Default target module to dump. Override per-invocation via --target.
DEFAULT_TARGET = os.environ.get("ATLAS_TARGET_MODULE", "")


# ---- Helpers ---------------------------------------------------------------

def stub(verb: str, args: argparse.Namespace) -> int:
    """Placeholder implementation."""
    print(f"[atlas {verb}] stub — args={vars(args)}", file=sys.stderr)
    print(f"[atlas {verb}] atlas_root={ATLAS_ROOT}", file=sys.stderr)
    print(f"[atlas {verb}] project_root={PROJECT_ROOT}", file=sys.stderr)
    return 0


def run(cmd: list[str], **kwargs) -> int:
    """subprocess.run with reasonable defaults; returns exit code."""
    print(f"[atlas] $ {' '.join(cmd)}", file=sys.stderr)
    return subprocess.run(cmd, **kwargs).returncode


# ---- Subcommands -----------------------------------------------------------

def cmd_dump(args: argparse.Namespace) -> int:
    """Run the full dump pipeline against the local lake project.

    Orchestrates `lake build` → `lake exe dumpdecls` → `dumpimports` →
    `run_dumptactics.py` → `ingest.py`. Writes dump JSON under
    `<project>/blueprint/`, then ingests into the kuzu DB.

    --target <module> selects the library to dump (replaces hardcoded
    `import Geometry` in the Lean dumpers — see the dumper-
    parameterisation TODO).
    --sha <SHA> tags the dump with a git SHA (defaults to
    `git rev-parse HEAD`).
    --watch re-runs on file change (not yet implemented).
    """
    return stub("dump", args)


def cmd_import(args: argparse.Namespace) -> int:
    """Add a previously-produced dump (JSON or directory) to the kuzu DB.

    Useful for SHA-connected history: import an old dump alongside the
    current one and let the viewer diff. With no args, imports the
    current `<project>/blueprint/`.
    """
    return stub("import", args)


def cmd_serve(args: argparse.Namespace) -> int:
    """Serve the static viewer + annotation API over HTTP.

    Static files use layered resolution (project first, then atlas
    package) so a downstream repo only needs `blueprint/graph.json`
    to get the full viewer. The annotation API (`/api/flags`,
    `/api/notes`) is backed by SQLite at
    `<project>/blueprint/atlas.sqlite`, kept out of the
    `just graph` regen path so reviewer notes survive a rebuild.

    Listens on `0.0.0.0:<port>` by default so the server is reachable
    from other hosts on the LAN once the local firewall is opened:

        sudo nixos-firewall-tool open tcp 8765

    Set `--host 127.0.0.1` to bind loopback-only.
    """
    # Lazy import so non-serve subcommands don't pay Flask startup cost.
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from serve_app import serve as _serve
    return _serve(ATLAS_ROOT, PROJECT_ROOT, args.host, args.port)


def cmd_query(args: argparse.Namespace) -> int:
    """Run an ad-hoc Cypher query against the kuzu DB.

    `atlas query "MATCH (n) RETURN count(n)"`
    `atlas query @<file>`  — read query from file
    """
    return stub("query", args)


def cmd_q(args: argparse.Namespace) -> int:
    """Run a bundled query by name (replaces `q.sh`).

    `atlas q sorry_blocked`
    `atlas q --list`        — list bundled queries
    """
    return stub("q", args)


def cmd_show(args: argparse.Namespace) -> int:
    """Print one decl's metadata + commentary fields.

    `atlas show proposition 3.4`
    `atlas show lemma 1.0.31`
    """
    return stub("show", args)


def cmd_stats(args: argparse.Namespace) -> int:
    """Feature-coverage report against the dump.

    Cross-checks the dump's marker / kind / atlasNum / commentary-field
    incidence against the Atlas feature registries. Prints a table of
    ✓ / ✗ per feature with first sample. CI-friendly exit code
    (non-zero if anything's missing).
    """
    return stub("stats", args)


def cmd_check(args: argparse.Namespace) -> int:
    """Sanity scan over the dump.

    Reports: orphaned commentary blocks (no target decl), paired-decl
    ambiguities (one commentary, multiple decls), markers without a
    containing decl, `sorry`s outside expected places.
    """
    return stub("check", args)


def cmd_db_init(args: argparse.Namespace) -> int:
    """Create the kuzu DB schema (replaces ad-hoc `schema.cypher` runs)."""
    return stub("db init", args)


def cmd_db_reset(args: argparse.Namespace) -> int:
    """Drop the kuzu DB."""
    return stub("db reset", args)


def cmd_version(args: argparse.Namespace) -> int:
    """Print version info."""
    print("atlas-cli v0.1.0 (skeleton)")
    print(f"atlas_root: {ATLAS_ROOT}")
    return 0


# ---- argparse wiring -------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="atlas",
        description="Atlas CLI — book-style theorem metadata + viewer.",
    )
    sub = p.add_subparsers(dest="verb", required=True, metavar="VERB")

    # dump
    p_dump = sub.add_parser("dump", help="run the dump pipeline")
    p_dump.add_argument("--target", default=DEFAULT_TARGET,
                        help="target Lean module (default: $ATLAS_TARGET_MODULE)")
    p_dump.add_argument("--sha", default=None,
                        help="tag dump with this git SHA (default: git rev-parse HEAD)")
    p_dump.add_argument("--watch", action="store_true",
                        help="re-run on file change (not yet implemented)")
    p_dump.set_defaults(func=cmd_dump)

    # import
    p_imp = sub.add_parser("import", help="import a dump into the kuzu DB")
    p_imp.add_argument("path", nargs="?", default=None,
                       help="dump file or directory (default: <project>/blueprint/)")
    p_imp.set_defaults(func=cmd_import)

    # serve. Port 8765 is the canonical "atlas serve" port — document it
    # everywhere so `nixos-firewall-tool open tcp 8765` works out of the
    # box. Host defaults to 0.0.0.0 so the firewall opening actually
    # buys you something; pass `--host 127.0.0.1` for loopback-only.
    p_srv = sub.add_parser("serve", help="serve the static viewer")
    p_srv.add_argument("--port", type=int, default=8765,
                       help="HTTP port (default 8765 — the canonical atlas port)")
    p_srv.add_argument("--host", default="0.0.0.0",
                       help="bind address (default 0.0.0.0 — all interfaces)")
    p_srv.add_argument("--watch", action="store_true",
                       help="auto re-dump + re-import on change (not yet implemented)")
    p_srv.set_defaults(func=cmd_serve)

    # query / q
    p_qry = sub.add_parser("query", help="run an ad-hoc Cypher query")
    p_qry.add_argument("cypher", help="Cypher query string, or @<file>")
    p_qry.set_defaults(func=cmd_query)

    p_q = sub.add_parser("q", help="run a bundled Cypher query by name")
    p_q.add_argument("name", nargs="?", default=None,
                     help="bundled query name (omit to list)")
    p_q.add_argument("--list", action="store_true", help="list bundled queries")
    p_q.set_defaults(func=cmd_q)

    # show
    p_show = sub.add_parser("show", help="print one decl's metadata")
    p_show.add_argument("kind", help="atlas kind (proposition / lemma / ...)")
    p_show.add_argument("num", help="atlas number (3.4, 1.0.31, B-1a, ...)")
    p_show.set_defaults(func=cmd_show)

    # stats
    p_stats = sub.add_parser("stats", help="feature-coverage report")
    p_stats.add_argument("--json", action="store_true",
                         help="emit JSON instead of a table")
    p_stats.set_defaults(func=cmd_stats)

    # check
    p_check = sub.add_parser("check", help="sanity scan over the dump")
    p_check.set_defaults(func=cmd_check)

    # db init / db reset
    p_db = sub.add_parser("db", help="kuzu DB operations")
    db_sub = p_db.add_subparsers(dest="db_verb", required=True, metavar="DB_VERB")
    p_db_init = db_sub.add_parser("init", help="create the kuzu DB schema")
    p_db_init.set_defaults(func=cmd_db_init)
    p_db_reset = db_sub.add_parser("reset", help="drop the kuzu DB")
    p_db_reset.set_defaults(func=cmd_db_reset)

    # version
    p_ver = sub.add_parser("version", help="print version info")
    p_ver.set_defaults(func=cmd_version)

    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
