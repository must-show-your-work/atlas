---
name: Atlas term-position keywords cannot shadow command keywords
description: Why `Atlas.lean` doesn't expose `lemma N.K` / `axiom N.K` / `theorem N.K` as term-position references — and how to add new kinds safely.
type: feedback
originSessionId: b2c5b236-d177-419d-ba65-917e999e75a8
---
`Atlas.lean` exposes term-position keyword references for atlas kinds
(`proposition 3.4`, `corollary 3.4`, `definition 0.3`, etc.) via
`syntax:max "<kind>" atlasNum : term`. It deliberately does *not* expose
this for `theorem` / `lemma` / `axiom`.

**Why:** declaring `"lemma"` (or `"theorem"`, `"axiom"`) as a term-position
parser token registers it in Lean's keyword table in a way that breaks
command-position parsing of bare `lemma X.Y {b : T} : … := …` /
`axiom X : …`. The error surfaces downstream as
`unexpected token '{'; expected '.'` on the `{` of the first bracketed
binder — Lean's `declId` parser gets confused once the keyword is
shadowed at term position. Same applies to any future kind whose name
collides with a Lean/Mathlib command keyword (`def`, `instance`,
`class`, `structure`, `inductive`, etc. — though we use `definition`
not `def`, which is safe).

**How to apply:** when adding a new atlas kind to the term-elab table
in `Atlas.lean`, first check whether the word is also a command-level
keyword. If yes, omit the `syntax:max "<kind>" atlasNum : term` line
and document that callers must use the French-quoted title form for
that kind. The *command*-position form (`atlas lemma "…"` / `atlas
axiom "…"`) is fine — the leading `"atlas"` token disambiguates, and
the kind is parsed with `rawIdent` which accepts keyword tokens
without reserving them.

There is an explanatory comment in `Atlas.lean` next to the term
syntax block; keep it accurate if the policy changes.
