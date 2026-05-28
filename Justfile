# Default: build Atlas + AtlasTest.
default: build

# Build the Atlas library and its smoke test.
build:
    lake build Atlas AtlasTest

# Run the smoke test. AtlasTest.lean is structured around `#check` /
# `#eval` directives that print on a clean build — the build itself
# is the test. Rebuilding from scratch (after `just clean`) is the
# most thorough check.
test:
    lake build AtlasTest

# Wipe Lake's build cache. Use before `just build` if you need a true
# from-scratch elaboration (e.g. to verify the macros + env extension
# still wire up without relying on stale `.olean`s).
clean:
    lake clean

# Refresh `lake-manifest.json` to whatever Mathlib HEAD currently is.
# Mathlib is pinned by manifest, so this is a deliberate bump.
update:
    lake update

# ---------------------------------------------------------------------
# Graph / display pipeline (checkpointed from GIYF).
#
# These recipes will not work as-is in a standalone Atlas package —
# the Lean dumpers in `scripts/` hardcode `import Geometry` and the
# Python pipeline expects `blueprint/`-relative paths. See
# CHECKPOINT.md for what needs adapting when Atlas truly migrates.
# ---------------------------------------------------------------------

# Rebuild the theorem graph database from a clean Lean build.
# Requires `nix develop` so `kuzu` (CLI + Python) and venv are on PATH.
graph:
    lake build
    lake exe dumpdecls
    lake exe dumpimports
    -python scripts/run_dumptactics.py
    python scripts/ingest.py
    python scripts/export_graph.py

# Serve the static dep-graph viewer over HTTP (browsers block `file://`
# `fetch` of sibling JSON, so a local server is the path of least
# resistance). Assumes `just graph` has produced blueprint/graph.json.
graph-view port="8765":
    @echo "Open http://localhost:{{port}}/scripts/graph.html"
    @python -m http.server {{port}}

# Run a bundled query, or list them when called with no name.
#   `just q`              — list all queries with one-line descriptions
#   `just q sorry_blocked`— print the query's legend, then run it
q name="":
    @./scripts/q.sh "{{name}}"
