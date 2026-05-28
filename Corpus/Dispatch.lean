/-
Corpus/Dispatch.lean — paired-decl `via` dispatch + `ref` cascade.

Two paired decls share the same `(kind, num)` (using the sub-letter
disambiguator from `Corpus/Numbers.lean`). A consumer site dispatches
between them via `via` based on the expected return type.

Also exercises:
- The tier cascade on `ref` (a `theorem` lookup falls through to
  `corollary` when no theorem matches at that number).
- The exact-kind discipline on `via` (cascade disabled — must pick the
  kind explicitly).
-/

import Atlas

namespace Corpus.Dispatch

-- Paired propositions sharing book number 0.7 — disambiguated by
-- sub-letter. Each produces a distinct return type so `via` can pick
-- between them.
atlas proposition 0.7.i  "Paired prop i — returns True" : True := trivial
atlas proposition 0.7.ii "Paired prop ii — returns Nat = Nat" : (0 : Nat) = 0 := rfl

-- Consumer sites. `via` accepts the args and elaborates each candidate
-- against the expected return type, picking the one that fits.
example : True := via proposition 0.7.i
example : (0 : Nat) = 0 := via proposition 0.7.ii

-- Cascade fixture. A `theorem` at 0.8.1 falls through to the
-- `corollary` because there's no theorem at that number.
atlas corollary 0.8.1 "Cascade fixture — looked up as `theorem 0.8.1` too" : True := trivial

example : True := ref theorem 0.8.1   -- cascade T1 → T2 picks the corollary
example : True := ref corollary 0.8.1 -- direct hit

end Corpus.Dispatch
