// Impact analysis: every decl that transitively depends on <DECL>.
// Answers "if I rename / change / weaken X, what gets affected?".
// Swap the name in the WHERE clause to inspect different targets.
MATCH (d:Decl)-[:USES*1..]->(target:Decl {name: 'Geometry.Theory.Distinct.of_eq'})
RETURN DISTINCT d.name, d.file, d.kind, d.has_sorry
ORDER BY d.file, d.name;
