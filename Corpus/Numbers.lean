/-
Corpus/Numbers.lean — every `atlasNum` syntax form.

Each declaration is meaningless (proves `True := trivial`) — the point
is to exercise the parser + the `atlasNumToString` case-analysis on
every supported number shape. If a new `atlasNum` form is added in
`Atlas/Number.lean`, add a fixture line here.

Shapes covered (1:1 with the `syntax` declarations in `Atlas/Number.lean`):
- `scientific`            — `3.4`
- `scientific "." num`    — `2.0.1`
- `scientific "." ident`  — `3.1.i`, `3.1.a` (sub-letter disambiguator)
- `ident "." num`         — `I.1` (letter-prefixed axiom)
- `ident "-" num ident`   — `B-1a`, `B-4iii` (compound book label)
- `"[" str "]"`           — `["B.1.a"]` (bracketed-string fallback)
-/

import Atlas

namespace Corpus.Numbers

atlas lemma 3.4 "scientific form 3.4" : True := trivial
atlas lemma 2.0.1 "scientific.num form 2.0.1" : True := trivial
atlas lemma 3.1.i "scientific.ident form 3.1.i (roman sub-letter)" : True := trivial
atlas lemma 3.1.a "scientific.ident form 3.1.a (alpha sub-letter)" : True := trivial
atlas axiom I.1 "ident.num form I.1" : True
atlas axiom B-1a "ident-num-ident form B-1a" : True
atlas axiom B-4iii "ident-num-ident form B-4iii" : True
atlas axiom ["B.1.a"] "bracketed-string form B.1.a" : True

end Corpus.Numbers
