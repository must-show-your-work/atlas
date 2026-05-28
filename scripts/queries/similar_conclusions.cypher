// Pairs of decls with identical pretty-printed types (duplicate candidates).
// String equality on `type_pp`; coarse but good for finding accidental
// duplicates and `alias :=` shadows.
MATCH (a:Decl), (b:Decl)
WHERE a.name < b.name
  AND a.type_pp = b.type_pp
  AND a.type_pp <> ''
  AND a.kind IN ['theorem', 'def']
RETURN a.name, a.file, b.name, b.file, a.type_pp
ORDER BY a.file, a.name;
