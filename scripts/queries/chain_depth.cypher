// Top 20 decls by longest dep-DAG path beneath them (depth hotspots).
// Long chains tend to point at heavily-layered proof scaffolding.
MATCH path = (root:Decl)-[:USES*1..]->(leaf:Decl)
WHERE NOT EXISTS { MATCH (leaf)-[:USES]->(:Decl) }
WITH root, max(length(path)) AS depth
RETURN root.name, root.file, depth
ORDER BY depth DESC
LIMIT 20;
