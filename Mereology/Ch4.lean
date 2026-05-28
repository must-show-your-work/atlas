/-
Mereology / Chapter 4 — Atomism.

The optional final layer: an *atomistic* mereology assumes every
individual has at least one *atom* (minimal proper-part-having
individual) below it. Under this assumption, GEM models are
classified up to isomorphism by their atom set.

Numbering: Chapter 4, items 1–3. Theorem 4.3 is the classification
result — the cleanest statement of "mereology is just Boolean algebra
written in part-talk."

Proofs are stubs; commentary is full.
-/

import Mereology.Ch3

namespace Mereology.Ch4

open Atlas
open Mereology.Ch1 Mereology.Ch2 Mereology.Ch3

/-! ## Atom -/

atlas commentary := by
  ref definition 4.1
  name "Atom"
  preface "An atom is an individual with no proper parts."
  notes "Atoms are mereology's analogue of singleton sets. In a
non-atomistic model the universe might be \"gunky\" — infinitely
divisible — and have no atoms at all."

atlas definition 4.1 "Atom"
  (a : Ind) : Prop := ¬ ∃ x : Ind, x ≺ a

attribute [reducible] «Atom»


/-! ## Atomism -/

atlas commentary := by
  ref axiom 4.2
  name "Atomism"
  preface "Every individual has at least one atom as a part."
  notes "Optional axiom — assumed only in *atomistic* mereology. Without
it, models can be gunky (every part has further proper parts, ad
infinitum). With it, models are determined by their atom structure."
  tags ["axiom", "optional", "atomism"]

atlas axiom 4.2 "Atomism"
  : ∀ x : Ind, ∃ a : Ind, «Atom» a ∧ a ≼ x


/-! ## Atomic GEM ≅ non-empty powersets -/

atlas commentary := by
  ref theorem 4.3
  name "Atomic GEM models are non-empty powersets"
  preface "An atomistic GEM model is isomorphic to the lattice of
non-empty subsets of its atom set, ordered by inclusion."
  notes "The classification result for atomistic mereology. Map each
individual to the set of atoms below it; map each non-empty atom-set
to its fusion (3.1). Both directions preserve and reflect parthood,
giving a lattice isomorphism."
  tags ["theorem", "classification", "punchline"]

atlas theorem 4.3 "Atomic GEM models are non-empty powersets"
  : ∀ x y : Ind,
    x ≼ y ↔ (∀ a : Ind, «Atom» a → a ≼ x → a ≼ y) := by
  motivation "the punchline — mereology is just (nonempty) Boolean algebra, written in part-talk."
  cf "Stone's representation theorem for atomic complete Boolean algebras: every such algebra is a powerset."
  idea "forward direction is direct (transitivity 1.3). Reverse uses atomism (4.2) to supply enough atoms, plus extensionality (2.5) to conclude equality at the lattice level."
  intuition "think of `x ≼ y` as `(atoms of x) ⊆ (atoms of y)` — this theorem says that intuition is exact under atomism."
  sorry

end Mereology.Ch4
