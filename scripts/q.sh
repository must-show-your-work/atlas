#!/usr/bin/env bash
# Wrapper around the Kuzu DB:
#   `q` (no args)   — list every query with its one-line description
#   `q <name>`      — print the query's legend, then run it
#
# Runs the query via the kuzu Python driver in the project venv. The `kuzu`
# CLI binary (in the Nix dev shell) would also work, but the Python path
# avoids a PATH-dependency.
set -euo pipefail

QUERIES_DIR="scripts/queries"
DB_PATH="blueprint/graph.kuzu"

if [ "$#" -eq 0 ] || [ -z "${1:-}" ]; then
  printf "Available queries (run with \`just q <name>\`):\n\n"
  for f in "$QUERIES_DIR"/*.cypher; do
    name=$(basename "$f" .cypher)
    desc=$(awk '/^[[:space:]]*\/\//{
      sub(/^[[:space:]]*\/\/[[:space:]]?/, "");
      print; exit
    }' "$f")
    printf "  %-22s  %s\n" "$name" "$desc"
  done
  exit 0
fi

name="$1"
file="$QUERIES_DIR/$name.cypher"
if [ ! -f "$file" ]; then
  printf "no such query: %s\n" "$name" >&2
  printf "run \`just q\` (no args) to list available queries\n" >&2
  exit 1
fi

# Print the leading `//` comment block as a legend.
printf -- "--- %s ---\n" "$name"
awk '/^[[:space:]]*\/\//{
  sub(/^[[:space:]]*\/\/[[:space:]]?/, "");
  print "  " $0; next
} {exit}' "$file"
printf "\n"

exec .venv/bin/python scripts/run_query.py "$file" "$DB_PATH"
