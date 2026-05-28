/-
Mereology / Chapter 1 — Ground Mereology.

The three partial-order axioms on the parthood relation, the
definition of *proper part*, and the two basic propositions about
proper-part: asymmetry and transitivity.

This chapter is the foundation; everything in Ch2–4 builds on it.
The axioms are taken as primitive (no proof), the definition is
expanded as `Proper part`, and the two propositions are proved
directly from the axioms.

Numbering: Chapter 1, items 1–6.
-/

import Mereology.Preamble

namespace Mereology.Ch1

open Atlas

/-! ## Axioms -/

atlas commentary := by
  ref axiom 1.1
  name "Reflexivity of parthood"
  preface "Every individual is a part of itself."
  notes "Called the *improper* part. Without this axiom the proper-part
relation collapses to parthood and the distinction in 1.4 below is
meaningless."

atlas axiom 1.1 "Reflexivity of parthood"
  : ∀ x : Ind, x ≼ x


atlas commentary := by
  ref axiom 1.2
  name "Antisymmetry of parthood"
  preface "If x is a part of y and y is a part of x, then x and y are
the same individual."
  notes "Distinguishes mereology from a general preorder. Combined
with reflexivity and transitivity (1.1, 1.3), this makes ≼ a partial
order."

atlas axiom 1.2 "Antisymmetry of parthood"
  : ∀ x y : Ind, x ≼ y → y ≼ x → x = y


atlas commentary := by
  ref axiom 1.3
  name "Transitivity of parthood"
  preface "If x is a part of y and y is a part of z, then x is a part of z."

atlas axiom 1.3 "Transitivity of parthood"
  : ∀ x y z : Ind, x ≼ y → y ≼ z → x ≼ z


/-! ## Definition -/

atlas commentary := by
  ref definition 1.4
  name "Proper part"
  preface "x is a proper part of y when x is a part of y but distinct from y."
  notes "*Proper* picks out the strict version of parthood. Reflexive
parthood (x ≼ x) is *improper*."

atlas definition 1.4 "Proper part"
  (x y : Ind) : Prop := x ≼ y ∧ x ≠ y

attribute [reducible] «Proper part»

@[inherit_doc «Proper part»]
notation:50 (priority := high) x " ≺ " y => «Proper part» x y


/-! ## Propositions -/

atlas commentary := by
  ref proposition 1.5
  name "Asymmetry of proper part"
  preface "If x is a proper part of y, then y is not a proper part of x."
  notes "Direct consequence of antisymmetry (1.2). The key step is
that both directions of proper-part would force x = y by 1.2,
contradicting the distinctness clause in the definition."

atlas proposition 1.5 "Asymmetry of proper part"
  : ∀ x y : Ind, x ≺ y → ¬ y ≺ x := by
  idea "if both x ≺ y and y ≺ x held, antisymmetry (1.2) would force x = y, but proper part requires x ≠ y."
  intro x y xPpY yPpX
  obtain ⟨xPy, xNeY⟩ := xPpY
  obtain ⟨yPx, _⟩ := yPpX
  exact xNeY (ref axiom 1.2 x y xPy yPx)


atlas commentary := by
  ref proposition 1.6
  name "Transitivity of proper part"
  preface "If x is a proper part of y and y is a proper part of z, then
x is a proper part of z."
  notes "The ≼-component follows from transitivity of parthood (1.3).
The distinctness component is where the proper-part definition does
work: if x = z, then x ≼ y and y ≼ x by substitution, so x = y by
antisymmetry, contradicting x ≺ y."

atlas proposition 1.6 "Transitivity of proper part"
  : ∀ x y z : Ind, x ≺ y → y ≺ z → x ≺ z := by
  intro x y z xPpY yPpZ
  obtain ⟨xPy, xNeY⟩ := xPpY
  obtain ⟨yPz, _⟩ := yPpZ
  refine ⟨ref axiom 1.3 x y z xPy yPz, ?_⟩
  idea "to disprove x = z, substitute z := x and use antisymmetry on x ≼ y, y ≼ x to force x = y, contradicting proper part."
  intro xEqZ
  subst xEqZ
  exact xNeY (ref axiom 1.2 x y xPy yPz)

end Mereology.Ch1
