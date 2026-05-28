// Orphans: decls with no incoming USES edges (dead-code candidates).
// Excludes top-level chapter results (P1, P2, ..., Ex*, pasch); those are
// expected leaves. Tweak the regex filter for your namespace conventions.
MATCH (d:Decl)
WHERE NOT EXISTS { MATCH (:Decl)-[:USES]->(d) }
  AND d.kind IN ['theorem', 'def']
  AND NOT d.name =~ '.*\\.P[0-9]+$'
  AND NOT d.name =~ '.*\\.Ex[0-9]+.*'
  AND NOT d.name CONTAINS '.pasch'
RETURN d.name, d.file, d.kind
ORDER BY d.file, d.name;
