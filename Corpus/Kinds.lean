/-
Corpus/Kinds.lean — every atlas kind that appears in `kindTiers`.

One trivial fixture per kind, plus the exact-only kinds
(`alternate`, `definition`) that don't appear in the cascade table.
If `Atlas/Basic.lean::kindTiers` grows a new vocabulary entry, add a
fixture line here.

Numbering uses chapter `0` (the kind-fixture chapter) — `0.1.<index>`.
-/

import Atlas

namespace Corpus.Kinds

-- T1 (main results)
atlas theorem      0.1.1 "theorem fixture" : True := trivial
atlas proposition  0.1.2 "proposition fixture" : True := trivial
atlas postulate    0.1.3 "postulate fixture" : True := trivial
atlas lemma        0.1.4 "lemma fixture" : True := trivial
atlas axiom        0.1.5 "axiom fixture" : True
atlas exercise     0.1.6 "exercise fixture" : True := trivial
atlas law          0.1.7 "law fixture" : True := trivial
atlas principle    0.1.8 "principle fixture" : True := trivial
atlas fact         0.1.9 "fact fixture" : True := trivial
atlas scholium     0.1.10 "scholium fixture" : True := trivial

-- T2 (derived)
atlas corollary    0.2.1 "corollary fixture" : True := trivial
atlas consequence  0.2.2 "consequence fixture" : True := trivial
atlas claim        0.2.3 "claim fixture" : True := trivial

-- T3 (commentary)
atlas remark       0.3.1 "remark fixture" : True := trivial
atlas note         0.3.2 "note fixture" : True := trivial
atlas observation  0.3.3 "observation fixture" : True := trivial
atlas example      0.3.4 "example fixture" : True := trivial
atlas discussion   0.3.5 "discussion fixture" : True := trivial

-- Exact-only (no cascade)
atlas alternate    0.4.1 "alternate fixture" : True := trivial
atlas definition   0.4.2 "definition fixture" : True := trivial

end Corpus.Kinds
