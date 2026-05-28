/-
# Corpus — fixture-style coverage of every Atlas feature.

One file per feature class, each kept small enough to elaborate fast
and readable enough that someone debugging a regression can find the
fixture and inspect it.

If you add an Atlas feature (new syntax form, new marker kind, new
commentary field, new tier vocabulary entry), add a corresponding
fixture line under the matching `Corpus/*.lean` so the dump → JSON
→ viewer pipeline gets coverage.

The companion to this is a small mathematical theory in some other
top-level lib (e.g. `Combinatory/`, `Conway/`, or whatever the author
picks) — that's where the end-to-end "does the viewer render
something beautiful?" demo lives. Corpus is the fixture suite;
the demo theory is the showcase.
-/

import Corpus.Numbers
import Corpus.Kinds
import Corpus.Markers
import Corpus.Commentary
import Corpus.Dispatch
