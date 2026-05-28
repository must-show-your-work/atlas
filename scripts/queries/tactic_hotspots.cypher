// Per-decl tactic-use counts (proof-style fingerprint).
// Heavy `obvious` / `aesop` use ⇒ implicit complexity hiding; many `sorry`s
// ⇒ unfinished. Requires the (currently-stub) `dumptactics` pass.
MATCH (d:Decl)-[u:USED_TACTIC]->(t:Tactic)
WITH d, t.name AS tactic, sum(u.count) AS uses
RETURN d.name, d.file, tactic, uses
ORDER BY d.file, d.name, uses DESC;
