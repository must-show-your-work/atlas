#!/usr/bin/env python3
"""
Export the term-level theorem graph as Cytoscape.js-shaped JSON for the
static HTML viewer at `blueprint/graph.html`.

By default the export applies two cleanup passes:
  1. Kind-filter — drops edges where a theorem merely names a
     foundational definition (e.g. `Point`, `Line`, `Segment`).
  2. Transitive reduction — drops "shortcut" edges. If A → B and
     B → C, the direct edge A → C is redundant (the chain through B
     already establishes the dependency) and so is suppressed.

Flags:
  --full        — disable both passes; emit every USES edge.
  --no-reduce   — apply the kind filter but skip transitive reduction.

Output: blueprint/graph.json with the shape:
  {
    "nodes": [{"data": {"id", "label", "kind", "file", "module",
                        "has_sorry", "doc", ...}}],
    "edges": [{"data": {"source", "target"}}]
  }
"""

from __future__ import annotations
import json
import sys
from pathlib import Path

import kuzu


PROJECT_ROOT = Path(__file__).resolve().parent.parent
BLUEPRINT_DIR = PROJECT_ROOT / "blueprint"
DB_PATH = BLUEPRINT_DIR / "graph.kuzu"
OUT = BLUEPRINT_DIR / "graph.json"


# ---------------------------------------------------------------------------
# Edge-filter heuristic. Keep edges that capture meaningful structural
# dependence; drop edges where a theorem merely references a foundational
# definition (e.g. theorem `P4` "uses" `Point` and `Line` only because they
# appear in its signature).
#
# Edit `KEEP_RULES` to retune. Each entry is (source_kind, allowed_target_kinds).
# Source kinds not listed default to "keep everything" (conservative).
# ---------------------------------------------------------------------------
KEEP_RULES: dict[str, set[str]] = {
    "axiom":   {"axiom", "def"},
    "def":     {"axiom", "def"},
    "theorem": {"axiom", "theorem"},   # ← drops theorem→def edges
    "opaque":  {"axiom", "def", "theorem", "opaque"},
}

# "Atmospheric" declarations — universal primitives that every theorem in
# the project mentions, so showing edges into them is informationally empty.
# Drop both incoming edges and the node itself (if it becomes isolated).
# Edit the set to tweak; e.g. add `"Geometry.Theory.Line"` if you decide
# the type-level def is also noise.
ATMOSPHERIC: set[str] = {
    "Geometry.Theory.Point",
    "Geometry.Theory.Between",
}


def keep_edge(src_kind: str | None, dst_kind: str | None) -> bool:
    if src_kind is None or dst_kind is None:
        return True
    allowed = KEEP_RULES.get(src_kind)
    if allowed is None:
        return True
    return dst_kind in allowed


def is_undocumented_def(kind: str | None, doc: str | None) -> bool:
    """A `def` with no docstring is treated as plumbing (auto-generated
    projections, instance fields, etc.) and dropped from the graph."""
    if kind != "def":
        return False
    return not (doc and doc.strip())


def has_underscore_prefix(name: str) -> bool:
    """A decl whose final dotted component begins with `_` is treated
    as compiler/user-private (`_proof_1`, `_eq_def`, `_aux_lemma`,
    etc.) and dropped from the graph regardless of kind."""
    last = name.rsplit(".", 1)[-1]
    return last.startswith("_")


def is_undocumented_projection(
    name: str,
    doc: str | None,
    all_names: set[str],
) -> bool:
    """A decl whose name is `X.Y` where `X` is also a tracked decl
    and which has no docstring is almost certainly an auto-generated
    structure field / projection (e.g., `Collinear.mem`, `Distinct.fst`).
    Folds back into its parent in the graph.

    Documented sub-lemmas (`Collinear.subset`, `Collinear.insert`,
    etc.) keep their own nodes — the docstring is the user signalling
    that this thing is interesting on its own."""
    if "." not in name:
        return False
    parent, _last = name.rsplit(".", 1)
    if parent not in all_names:
        return False
    return not (doc and doc.strip())


def bridge_around(edges: list[tuple[str, str]],
                  dropped: set[str]) -> list[tuple[str, str]]:
    """Remove every edge incident to a dropped node, but first preserve
    reachability through it: each (u → n) + (n → v) becomes (u → v).
    Deduplicates the result. Self-edges are discarded."""
    from collections import defaultdict
    incoming: dict[str, set[str]] = defaultdict(set)
    outgoing: dict[str, set[str]] = defaultdict(set)
    for u, v in edges:
        incoming[v].add(u)
        outgoing[u].add(v)

    new_edges: set[tuple[str, str]] = set()
    for u, v in edges:
        if u in dropped or v in dropped:
            continue
        new_edges.add((u, v))
    for n in dropped:
        for u in incoming[n]:
            if u in dropped:
                continue
            for v in outgoing[n]:
                if v in dropped or u == v:
                    continue
                new_edges.add((u, v))
    return list(new_edges)


# ---------------------------------------------------------------------------
# Transitive reduction. For each direct edge u → v, the edge is "redundant"
# if there's a longer path u → ... → v (length ≥ 2) using only other edges.
# In a DAG this produces the unique minimal edge set preserving reachability;
# our dep graph is a DAG by construction (no cyclic Lean definitions).
# ---------------------------------------------------------------------------
def transitive_reduce(edges: list[tuple[str, str]]) -> list[tuple[str, str]]:
    from collections import defaultdict
    adj: dict[str, set[str]] = defaultdict(set)
    for u, v in edges:
        adj[u].add(v)

    redundant: set[tuple[str, str]] = set()
    for u, v in edges:
        # DFS from u, skipping the direct edge u→v; if we can still reach v
        # via some other path, the direct edge is redundant.
        stack = [w for w in adj[u] if w != v]
        seen = {u}
        while stack:
            x = stack.pop()
            if x == v:
                redundant.add((u, v))
                break
            if x in seen:
                continue
            seen.add(x)
            stack.extend(adj[x])
    return [(u, v) for (u, v) in edges if (u, v) not in redundant]


def main() -> None:
    full = "--full" in sys.argv[1:]
    skip_reduce = "--no-reduce" in sys.argv[1:]
    conn = kuzu.Connection(kuzu.Database(str(DB_PATH)))

    # Pre-load SubVerso-emitted highlighted HTML per decl (produced by
    # `lake exe dumptactics`). Optional: if the file's missing, every
    # decl just gets `source_html = None` and the viewer falls back to
    # the plain-text source slice.
    highlighted: dict[str, str] = {}
    hl_path = BLUEPRINT_DIR / "highlighted.json"
    if hl_path.exists():
        try:
            highlighted = json.loads(hl_path.read_text())
        except json.JSONDecodeError as e:
            print(f"warning: blueprint/highlighted.json is malformed ({e});"
                  " falling back to plain source", file=sys.stderr)

    nodes = []
    kind_of: dict[str, str] = {}
    doc_of: dict[str, str | None] = {}
    # Cache file contents to avoid re-reading the same file once per decl
    # (most modules house many decls).
    file_cache: dict[str, list[str]] = {}

    def read_source(file: str | None, ls: int | None, le: int | None) -> str | None:
        """Slice [ls..le] out of `file` (1-based, inclusive). Returns
        None if any input is missing or the file can't be read."""
        if not file or ls is None or le is None:
            return None
        if file not in file_cache:
            try:
                with open(PROJECT_ROOT / file, encoding="utf-8") as f:
                    file_cache[file] = f.readlines()
            except OSError:
                file_cache[file] = []
                return None
        lines = file_cache[file]
        if not lines:
            return None
        # Lean line numbers are 1-based; slice is inclusive of `le`.
        ls_i = max(0, ls - 1)
        le_i = min(len(lines), le)
        return "".join(lines[ls_i:le_i]).rstrip()

    rs = conn.execute(
        """
        MATCH (d:Decl)
        OPTIONAL MATCH (d)-[:DECLARED_IN]->(m:Module)
        RETURN d.name, d.kind, d.file, m.name, d.namespace,
               d.has_sorry, d.is_proposition, d.doc, d.type_pp,
               d.line_start, d.line_end,
               d.atlas_kind, d.atlas_number, d.atlas_title
        """
    )
    while rs.has_next():
        (name, kind, file, module, ns, has_sorry, is_prop, doc, type_pp,
         ls, le, atlas_kind, atlas_number, atlas_title) = rs.get_next()
        kind_of[name] = kind
        doc_of[name] = doc
        label = name.split(".")[-1]
        source_text = read_source(file, ls, le)
        nodes.append({
            "data": {
                "id": name,
                "label": label,
                "kind": kind,
                "file": file,
                "module": module,
                "namespace": ns,
                "has_sorry": bool(has_sorry),
                "is_proposition": bool(is_prop),
                "doc": doc,
                "type_pp": type_pp,
                "line_start": ls,
                "line_end": le,
                "source": source_text,
                "source_html": highlighted.get(name),
                # Atlas attribute metadata (None when the decl carries no
                # `@[atlas …]`). The viewer keys off `atlas_kind` to decide
                # whether to render the book-style card chrome.
                "atlas_kind": atlas_kind,
                "atlas_number": atlas_number,
                "atlas_title": atlas_title,
            }
        })

    raw_edges = []
    rs = conn.execute("MATCH (a:Decl)-[:USES]->(b:Decl) RETURN a.name, b.name")
    while rs.has_next():
        src, dst = rs.get_next()
        raw_edges.append((src, dst))

    # Decls to suppress entirely.
    #   1. Undocumented `def`s — Lean's auto-generated projections /
    #      instance fields / opaque internal helpers; the user marks
    #      the defs they actually care about with a docstring.
    #   2. Decls whose final component begins with `_` — compiler
    #      proof obligations (`_proof_1`), elaboration aux defs, etc.
    #   3. Undocumented `X.Y` decls where `X` is itself tracked —
    #      auto-projections like `Collinear.mem`. Fold to the parent.
    undoc_defs: set[str] = set()
    underscore_decls: set[str] = set()
    undoc_projections: set[str] = set()
    if not full:
        all_names = set(kind_of.keys())
        undoc_defs = {
            n for n in kind_of
            if is_undocumented_def(kind_of.get(n), doc_of.get(n))
        }
        underscore_decls = {n for n in kind_of if has_underscore_prefix(n)}
        undoc_projections = {
            n for n in kind_of
            if is_undocumented_projection(n, doc_of.get(n), all_names)
        }

    if full:
        kept = raw_edges
        kind_dropped = 0
        atmos_dropped = 0
        undoc_dropped = 0
    else:
        # Pass 1: kind filter.
        kept = [(s, d) for s, d in raw_edges
                if keep_edge(kind_of.get(s), kind_of.get(d))]
        kind_dropped = len(raw_edges) - len(kept)
        # Pass 1b: atmospheric filter (drop edges to universal primitives).
        before = len(kept)
        kept = [(s, d) for s, d in kept if d not in ATMOSPHERIC]
        atmos_dropped = before - len(kept)
        # Pass 1c: bridge around plumbing decls (undocumented defs,
        # underscore-prefixed compiler decls, undocumented projections).
        # Keeps `A → useful` even if A went through one of these on its
        # way to a meaningful target.
        before = len(kept)
        kept = bridge_around(
            kept, undoc_defs | underscore_decls | undoc_projections)
        undoc_dropped = before - len(kept)

    if full or skip_reduce:
        final = kept
        reduce_dropped = 0
    else:
        final = transitive_reduce(kept)
        reduce_dropped = len(kept) - len(final)

    edges = [{"data": {"source": s, "target": d}} for s, d in final]

    # Drop nodes that have no remaining edges (atmospheric leftovers,
    # undocumented defs, and anything orphaned by the filtering passes).
    if not full:
        connected: set[str] = set()
        for e in edges:
            connected.add(e["data"]["source"])
            connected.add(e["data"]["target"])
        nodes_kept = [
            n for n in nodes
            if n["data"]["id"] in connected
            and n["data"]["id"] not in undoc_defs
            and n["data"]["id"] not in underscore_decls
            and n["data"]["id"] not in undoc_projections
        ]
        node_dropped = len(nodes) - len(nodes_kept)
        nodes = nodes_kept
    else:
        node_dropped = 0

    OUT.write_text(json.dumps({"nodes": nodes, "edges": edges}, indent=2))

    if full:
        mode = "full"
    elif skip_reduce:
        mode = "kind+atmospheric filtered, no reduction"
    else:
        mode = "kind+atmospheric filtered + transitively reduced"
    print(
        f"Exported {len(nodes)} nodes / {len(edges)} edges → {OUT}\n"
        f"  mode: {mode}\n"
        f"  raw edges: {len(raw_edges)};"
        f"  kind-drop: {kind_dropped};"
        f"  atmospheric-drop: {atmos_dropped};"
        f"  plumbing-bridge: {undoc_dropped}"
        f" ({len(undoc_defs)} undoc-defs"
        f" / {len(underscore_decls)} underscore"
        f" / {len(undoc_projections)} undoc-projections);"
        f"  transitive-drop: {reduce_dropped};"
        f"  isolated-nodes-drop: {node_dropped}"
    )


if __name__ == "__main__":
    main()
