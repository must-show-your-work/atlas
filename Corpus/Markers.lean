/-
Corpus/Markers.lean — every inline marker tactic.

One trivial proof body that invokes each marker kind exactly once, so
the dump round-trips and the viewer can render all 13 kinds. Markers
are tactic-position-only; they no-op semantically.

Kinds covered (1:1 with `Atlas/Markers.lean`):
- Original family: `quoting (N) "..."`, `quoting ... "..."`,
  `comment "..."`, `page break`.
- Reader-cue (extended): `idea`, `intuition`, `motivation`, `caution`,
  `aside`, `cf`, `see also`.
- Code-state (extended): `todo`, `fixme`, `detail`.
-/

import Atlas

namespace Corpus.Markers

atlas lemma 0.5.1 "Exercises every marker kind in a single proof" : True := by
  -- Original family.
  quoting (1) "explicit step number"
  quoting ... "continuation of previous step"
  comment "author commentary, position-anchored"
  page break

  -- Reader-cue.
  idea "the key insight of the proof"
  intuition "mental picture the reader should hold"
  motivation "why this lemma is worth proving"
  caution "thing readers commonly miss"
  aside "tangent / context"
  cf "informal cross-reference"
  see also "alternate prose form of cf"

  -- Code-state.
  todo "future work to do"
  fixme "known broken placeholder"
  detail "implementation-detail question"

  trivial

end Corpus.Markers
