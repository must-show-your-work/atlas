#!/usr/bin/env python3
"""Orchestrator for `lake exe dumptactics`.

Discovers every `Geometry/**.lean` and runs `lake exe dumptactics
MOD` as a fresh subprocess per module. Each invocation imports
Mathlib from scratch, processes its single module, writes its cache
file, and exits — so RAM is fully released between modules instead of
accumulating.

Each subprocess runs at the lowest CPU + I/O priority and is capped
by `ulimit -v` so a runaway elaboration (Mathlib unifier exploding,
etc.) gets killed by the kernel before it can hang the system. The
per-subprocess cap is conservative-but-generous so legitimate heavy
modules still complete.

After all subprocesses run (or fail individually), the per-module
cache files in `blueprint/highlighted-cache/` are concatenated into
the two master files that `export_graph.py` consumes:

  - blueprint/highlighted.json — { decl_name: html_string }
  - blueprint/tactics.json     — [{ decl, tactic, line }, …]

Modules with an up-to-date cache are skipped at the Python layer (no
subprocess started) so re-running after a touched-source edit only
spends time on the actually-changed files.
"""
from __future__ import annotations
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GEO_DIR = ROOT / "Geometry"
CACHE_DIR = ROOT / "blueprint" / "highlighted-cache"
BP_DIR = ROOT / "blueprint"

# Path to a shell that understands `ulimit` (a POSIX shell builtin).
# `subprocess.run(executable=…)` defaults to `/bin/sh` which doesn't
# exist on NixOS in the usual place, so resolve via PATH instead.
SHELL = shutil.which("bash") or shutil.which("sh")
if SHELL is None:
    sys.exit("run_dumptactics: no bash/sh on PATH")

# Per-subprocess virtual-memory cap in KB. 12 GB is comfortably above
# a Mathlib import + Geometry elaboration but well under the box's
# total RAM, so a runaway gets killed instead of swap-thrashing the
# whole system.
ULIMIT_V_KB = 12_000_000


def discover_modules() -> list[str]:
    """Return dotted module names for every `Geometry/**.lean` file."""
    out: list[str] = []
    for p in GEO_DIR.rglob("*.lean"):
        rel = p.relative_to(ROOT)
        dotted = str(rel.with_suffix("")).replace("/", ".")
        out.append(dotted)
    return sorted(out)


def cache_file(mod: str) -> Path:
    return CACHE_DIR / f"{mod}.cache"


def src_file(mod: str) -> Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def cache_up_to_date(mod: str) -> bool:
    """True if the per-module cache is strictly newer than the source.
    Mirrors `DumpTactics.lean`'s `cacheUpToDate` so the Python layer
    can short-circuit before paying subprocess-startup cost."""
    cf = cache_file(mod)
    if not cf.exists():
        return False
    sf = src_file(mod)
    if not sf.exists():
        # Source disappeared but cache stayed; trust the cache.
        return True
    return cf.stat().st_mtime > sf.stat().st_mtime


def run_one(mod: str, idx: int, total: int) -> int:
    """Spawn `lake exe dumptactics MOD` in a niced/ulimited subprocess.
    Returns the exit code (non-zero ≠ fatal here; we just log and move
    on so one bad module doesn't block the rest)."""
    cmd = (
        f"ulimit -v {ULIMIT_V_KB} && "
        f"nice -n 19 ionice -c 3 "
        f"env LEAN_NUM_THREADS=1 lake exe dumptactics {mod}"
    )
    print(f"[run_dumptactics] [{idx}/{total}] {mod}", flush=True)
    r = subprocess.run(cmd, shell=True, executable=SHELL, cwd=ROOT)
    if r.returncode != 0:
        print(
            f"[run_dumptactics] [{idx}/{total}] {mod} → exit {r.returncode} "
            f"(continuing; partial cache, if any, preserved)",
            flush=True,
        )
    return r.returncode


def parse_cache(path: Path) -> tuple[list[str], list[str]]:
    """Read a per-module cache file and return its (html_entries,
    tactic_entries) lists. Entries are pre-formatted JSON fragments
    ready to drop into the master arrays."""
    html: list[str] = []
    tactics: list[str] = []
    sect: str | None = None
    version_ok = False
    saw_version = False
    for line in path.read_text().splitlines():
        if line == "__VERSION__":
            sect = "version"
        elif line == "__HTML__":
            sect = "html"
        elif line == "__TACTICS__":
            sect = "tactics"
        elif sect == "version" and not saw_version:
            saw_version = True
            version_ok = (line.strip() == "v1")
        elif sect == "html" and line.startswith("  "):
            if version_ok:
                html.append(line)
        elif sect == "tactics" and line.startswith("  "):
            if version_ok:
                tactics.append(line)
    return html, tactics


def assemble_master() -> None:
    BP_DIR.mkdir(parents=True, exist_ok=True)
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    html_all: list[str] = []
    tactics_all: list[str] = []
    for cf in sorted(CACHE_DIR.glob("*.cache")):
        h, t = parse_cache(cf)
        html_all.extend(h)
        tactics_all.extend(t)
    html_master = "{\n" + ",\n".join(html_all) + "\n}\n"
    tactics_master = "[\n" + ",\n".join(tactics_all) + "\n]\n"
    (BP_DIR / "highlighted.json").write_text(html_master)
    (BP_DIR / "tactics.json").write_text(tactics_master)
    print(
        f"[run_dumptactics] assembled master: "
        f"{len(html_all)} decls, {len(tactics_all)} tactic occurrences",
        flush=True,
    )


def main() -> int:
    mods = discover_modules()
    print(f"[run_dumptactics] discovered {len(mods)} modules", flush=True)
    skipped = 0
    failed = 0
    for i, mod in enumerate(mods, 1):
        if cache_up_to_date(mod):
            skipped += 1
            print(f"[run_dumptactics] [{i}/{len(mods)}] {mod} (cached)",
                  flush=True)
            continue
        rc = run_one(mod, i, len(mods))
        if rc != 0:
            failed += 1
    print(f"[run_dumptactics] done: "
          f"{skipped} cached, {len(mods) - skipped - failed} processed, "
          f"{failed} failed", flush=True)
    assemble_master()
    return 0


if __name__ == "__main__":
    sys.exit(main())
