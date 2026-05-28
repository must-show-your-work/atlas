// Cross-module USES-edge counts (top 30 module pairs by edge weight).
// High inter-module weight = wide surface area between those files;
// high intra-module weight (not shown) = high cohesion.
MATCH (src:Decl)-[:USES]->(dst:Decl), (src)-[:DECLARED_IN]->(srcMod:Module),
      (dst)-[:DECLARED_IN]->(dstMod:Module)
WHERE srcMod.name <> dstMod.name
RETURN srcMod.name AS from_mod, dstMod.name AS to_mod, count(*) AS edge_count
ORDER BY edge_count DESC
LIMIT 30;
