/-
Mereology / Chapter 3 — Sums and the Lattice Structure.

Where mereology becomes algebra. Unrestricted Fusion (Axiom 3.1)
asserts that any non-empty collection of individuals has a "sum" —
an individual whose parts are exactly the parts of the collection.
Combined with extensionality (2.5), this gives a complete lattice
structure on `Ind` under ≼.

Numbering: Chapter 3, items 1–4. Theorem 3.4 is the chapter's
punchline (and a hook for the Atlas demo): GEM is essentially a
Boolean algebra minus its bottom element.

Proofs are stubs; commentary is full.
-/

import Mereology.Ch2

namespace Mereology.Ch3

open Atlas
open Mereology.Ch1 Mereology.Ch2

/-! ## Unrestricted Fusion -/

atlas commentary := by
  ref axiom 3.1
  name "Unrestricted Fusion"
  preface "For every non-empty predicate φ on individuals, there
exists a *fusion* σ — an individual that overlaps exactly those things
which overlap some φ-instance."
  notes "*Unrestricted* because the existence of σ is asserted for
arbitrary φ. Restricted variants (only for φ definable in some
fragment) give weaker theories. We take the unrestricted form here
because it makes the lattice structure in 3.4 fall out cleanly."
  tags ["axiom", "fusion", "lattice"]

atlas axiom 3.1 "Unrestricted Fusion"
  : ∀ φ : Ind → Prop, (∃ w : Ind, φ w) →
    ∃ σ : Ind, ∀ y : Ind, O(y, σ) ↔ ∃ w : Ind, φ w ∧ O(y, w)


/-! ## Uniqueness of fusion -/

atlas commentary := by
  ref theorem 3.2
  name "Uniqueness of fusion"
  preface "Under supplementation, the fusion of a predicate is unique."
  notes "Existence comes from 3.1; uniqueness requires the extensionality
machinery from Ch2. Two fusions of the same φ would overlap the same
things, so by extensionality of overlap (a consequence of 2.5), they
are the same individual."

atlas theorem 3.2 "Uniqueness of fusion"
  : ∀ (φ : Ind → Prop) (σ₁ σ₂ : Ind),
    (∀ y : Ind, O(y, σ₁) ↔ ∃ w : Ind, φ w ∧ O(y, w)) →
    (∀ y : Ind, O(y, σ₂) ↔ ∃ w : Ind, φ w ∧ O(y, w)) →
    σ₁ = σ₂ := by
  idea "σ₁ and σ₂ overlap the same things; combine with extensionality of proper parts (2.5) to conclude σ₁ = σ₂."
  sorry


/-! ## Binary sum -/

atlas commentary := by
  ref corollary 3.3
  name "Binary sum"
  preface "Any two individuals have a sum: an individual that overlaps
exactly the things that overlap either input."
  notes "Specialise Unrestricted Fusion to the predicate `λ w. w = x ∨
w = y`. The fusion is the binary sum, written `x ⊔ y`."

atlas corollary 3.3 "Binary sum"
  : ∀ x y : Ind, ∃ z : Ind, ∀ w : Ind, O(w, z) ↔ O(w, x) ∨ O(w, y) := by
  idea "instantiate 3.1 with φ := (· = x ∨ · = y); the resulting σ is x ⊔ y."
  sorry


/-! ## Complete lattice -/

atlas commentary := by
  ref theorem 3.4
  name "GEM is a complete lattice"
  preface "The parthood relation on a GEM model is a complete lattice
under fusion (join) and product (meet, where defined)."
  notes "This is the chapter's payoff and the bridge to algebra. The
join of any family is the fusion (3.1); the meet of x and y is the
fusion of common parts when overlap holds. The lattice has a top (the
universe — fusion of all individuals) but no bottom — mereology has
no \"null individual\", unlike Boolean algebras."
  tags ["theorem", "lattice", "punchline"]

atlas theorem 3.4 "GEM is a complete lattice"
  : ∀ (S : Set Ind), S.Nonempty →
    ∃ σ : Ind, ∀ y : Ind, O(y, σ) ↔ ∃ w ∈ S, O(y, w) := by
  motivation "the chapter's payoff: parthood is more than a partial order — it's the order of a (nearly) Boolean algebra."
  cf "Stone duality: atomic complete Boolean algebras are exactly powersets. GEM minus bottom is the same picture (4.3)."
  idea "take φ := (· ∈ S) in 3.1."
  sorry

end Mereology.Ch3
