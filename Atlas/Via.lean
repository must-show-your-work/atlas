/-
Atlas/Via.lean — `via` as a surface alias of `ref`.

`via` and `ref` are interchangeable spellings of the same citation
form. Both accept the no-args and with-args shapes, both go through
the type-directed dispatch in `Atlas/Ref.lean`:

```
via kind N            -- expands to `ref kind N`
via kind N args+      -- expands to `ref kind N args+`
```

Historically `via` carried its own term-elab with an exact-kind lookup
and an `isDefEq` dispatch loop, separate from `ref`'s cascade-and-
choice-node logic. That split has been retired: position-aware,
type-directed dispatch lives in `Atlas/Ref.lean` and is reachable from
either keyword.

Depends on `Atlas/Ref.lean` (the expansion target).
-/

import Atlas.Ref

namespace Atlas

syntax:max (name := atlasVia) "via" rawIdent atlasNumLit : term
syntax:max (name := atlasViaApp)
  "via" rawIdent atlasNumLit (ppSpace colGt term:max)+ : term

macro_rules
  | `(via $k:ident $n:atlasNumLit)              => `(ref $k $n)
  | `(via $k:ident $n:atlasNumLit $arg $args*)  => `(ref $k $n $arg $args*)

end Atlas
