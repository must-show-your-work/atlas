#!/usr/bin/env python3
"""
Run a single .cypher file against the Kuzu DB and print results as a table.

Argv: <query_file> <db_path>
"""
from __future__ import annotations

import sys
from pathlib import Path

import kuzu


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: run_query.py <query.cypher> <db_path>", file=sys.stderr)
        return 1
    query_file = Path(sys.argv[1])
    db_path = sys.argv[2]
    query = query_file.read_text()

    conn = kuzu.Connection(kuzu.Database(db_path))
    result = conn.execute(query)
    cols = result.get_column_names()
    # Compute column widths from the first ~200 rows, then re-fetch.
    rows: list[list[str]] = []
    while result.has_next():
        rows.append([str(v) for v in result.get_next()])
    if not rows:
        print("(no results)")
        return 0
    widths = [max(len(c), *(len(r[i]) for r in rows)) for i, c in enumerate(cols)]
    sep = "  "
    print(sep.join(c.ljust(w) for c, w in zip(cols, widths)))
    print(sep.join("-" * w for w in widths))
    for r in rows:
        print(sep.join(cell.ljust(w) for cell, w in zip(r, widths)))
    print(f"\n({len(rows)} rows)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
