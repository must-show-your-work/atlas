/-
Smoke test for the top-level `Atlas` module. Defines a trivial
proposition via the macro and references it via both the elab term and
the French-quoted title to exercise the full pipeline (macro → attribute
→ env extension → reference lookup).

Delete or extend as the real migration progresses.
-/

import Mathlib.Tactic.Lemma
import Atlas

namespace AtlasTest

-- Coexistence: bare Mathlib `lemma` / Lean `axiom` parse correctly even
-- with `Atlas` imported. This is the side-by-side guarantee that lets a
-- mixed codebase migrate to `atlas lemma` / `atlas axiom` incrementally
-- without breaking call sites that haven't been touched yet.
lemma bare_simple : True := trivial
lemma bare_with_binder {n : Nat} : n = n := rfl
lemma bare_dotted.qualified {n : Nat} (h : n = n) : n = n := h
axiom bare_axiom : ∀ n : Nat, n + 0 = n

atlas proposition 0.1 "Reflexivity of Equality on Nat"
    : ∀ n : Nat, n = n := by intro _; rfl

-- Reference by elab term:
example : ∀ n : Nat, n = n := proposition 0.1

-- Reference by French-quoted title:
example : ∀ n : Nat, n = n := «Reflexivity of Equality on Nat»

-- Binder pass-through — `{n : Nat}` and `(h : ...)` survive the macro.
atlas lemma 0.2 "Equality is symmetric for Nat"
    {a b : Nat} (h : a = b) : b = a := by rw [h]

-- For `atlas lemma`/`atlas theorem`/`atlas axiom` refs, use either the
-- uniform `ref <kind> <num>` form (recommended) or the French-quoted
-- title. (`ref` is the leading-token for term-position atlas references;
-- `atlas` couldn't double as a term-position keyword without conflicting
-- with the command form they both lead.)
example {x y : Nat} (heq : x = y) : y = x := ref lemma 0.2 heq
example {x y : Nat} (heq : x = y) : y = x := «Equality is symmetric for Nat» heq

-- Mixed positional + implicit binders, def kind.
atlas definition 0.3 "Square of a Nat" (n : Nat) : Nat := n * n

#eval definition 0.3 7  -- expects 49

-- Theory-style lemma: every atlas decl must carry a number. The 3-part
-- `chapter.level.index` form is for theory lemmas without a book ref.
atlas lemma 0.0.1 "Addition associativity (Nat)"
    (a b c : Nat) : a + b + c = a + (b + c) := by ac_rfl

atlas lemma 2.0.1 "Three-part-numbered theory lemma test"
    (n : Nat) : n + 0 = n := by simp

example (n : Nat) : n + 0 = n := ref lemma 2.0.1 n
example (a b c : Nat) : a + b + c = a + (b + c) := ref lemma 0.0.1 a b c
-- The uniform form works for non-conflicting kinds too:
example : Nat := ref definition 0.3 5
example : ∀ n : Nat, n = n := ref proposition 0.1
-- French-quoted title still works as a fallback / disambiguator:
example (n : Nat) : n + 0 = n := «Three-part-numbered theory lemma test» n

#check «Addition associativity (Nat)»

-- Deep-dot syntax via the custom Parser: bare serial-code IDs of any
-- shape work, including the previously-blocked `<digit>.<letter>`
-- boundaries that tripped Lean's standard tokenizer.
atlas lemma 3.4 "depth-2 num.num" : True := trivial
atlas lemma 3.0.5 "depth-3 num.num.num" : True := trivial
atlas lemma 3.0.5.a "depth-4 with num.letter boundary — formerly blocked" : True := trivial
atlas lemma 3.Theory.5 "ident-section, num end — formerly blocked" : True := trivial
atlas lemma 3.Theory.5.a "5-part with internal num.letter — formerly blocked" : True := trivial
atlas exercise 3.Review.3 "bare chapter.section.exNum" : True := trivial
atlas exercise 3.Review.3.a "with bullet" : True := trivial
atlas exercise 3.Review.3.a.i "Greenberg's full serial-code shape" : True := trivial
atlas axiom B.4.i "Greenberg axiom B-4(i) — formerly required brackets" : True

example : True := ref lemma 3.Theory.5
example : True := ref lemma 3.Theory.5.a
example : True := ref exercise 3.Review.3.a.i
example : True := ref axiom B.4.i

end AtlasTest
