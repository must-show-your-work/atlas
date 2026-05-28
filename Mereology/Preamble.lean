/-
Mereology/Preamble.lean — opaque universe, primitive parthood, notation.

The domain of discourse is `Ind` (individuals). Following the
Greenberg-in-GIYF pattern, we leave it as an opaque axiomatized type:
the formal content is parametric over any model satisfying the axioms,
and treating `Ind` as `axiom Ind : Type` makes that parametricity
explicit and prevents accidental use of computational structure.

Parthood `≼` is the sole primitive. Everything else (proper part,
overlap, disjointness, sum, atom) is defined.

No atlas decls here — this is foundational machinery, not book content.
Foundational primitives sit "below" the atlas system the same way
`Point` / `Line` do in GIYF's Geometry.Theory.Axioms.
-/

import Atlas

axiom Ind : Type

axiom parthood : Ind → Ind → Prop

@[inherit_doc parthood]
notation:50 (priority := high) x " ≼ " y => parthood x y
