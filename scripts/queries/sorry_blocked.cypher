// Decls "completed" only modulo `sorry`-bearing prerequisite work.
// Walks transitive dep chains from any decl with `has_sorry = true`.
MATCH (sorry_decl:Decl {has_sorry: true})<-[:USES*0..]-(blocked:Decl)
RETURN DISTINCT blocked.name, blocked.file, blocked.has_sorry AS itself_has_sorry
ORDER BY blocked.file, blocked.name;
