// Full transitive dep-closure beneath <DECL> (everything it needs).
// Substitute the name in the WHERE clause to target a different root.
MATCH (start:Decl {name: 'Geometry.Ch3.Prop.P4'})-[:USES*1..]->(d:Decl)
RETURN DISTINCT d.name, d.file, d.kind, d.has_sorry
ORDER BY d.file, d.name;
