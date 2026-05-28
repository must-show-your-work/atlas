/-
Corpus/Commentary.lean — every `atlas commentary` field.

Three fixtures exercising the full field surface:
- minimal: `ref` only (the bare minimum).
- typical: `ref` + `page` + `name` + `preface`.
- maximal: every field including multi-paragraph `notes` and the
  `pages low..high` range form.

If a new field is added to `acRef` / `acPage` / ... in
`Atlas/Commentary.lean`, add a line to the maximal fixture below.
-/

import Atlas

namespace Corpus.Commentary

open Atlas

-- Fixture targets — three trivial decls the blocks below reference.

atlas lemma 0.6.1 "minimal commentary target" : True := trivial
atlas lemma 0.6.2 "typical commentary target" : True := trivial
atlas lemma 0.6.3 "maximal commentary target" : True := trivial

-- Commentary blocks.

atlas commentary := by
  ref lemma 0.6.1

atlas commentary := by
  ref lemma 0.6.2
  page 42
  name "Typical commentary target"
  preface "A one-paragraph book statement, lifted from the source doc-comment."

atlas commentary := by
  ref lemma 0.6.3
  pages 100..103
  name "Maximal commentary target"
  aliases [Corpus.Commentary.maximalAlias, Corpus.Commentary.anotherAlias]
  preface "First paragraph of the book statement.

Second paragraph, after a blank line — Lean strings preserve newlines
so paragraph structure round-trips through the dump."
  notes "Editorial commentary distinct from the book preface.

Can also span paragraphs."
  tags ["fixture", "all-fields", "exhaustive"]

end Corpus.Commentary
