// Lemmas referenced by exactly one other decl (inlining candidates).
// Also: "is this auxiliary lemma actually earning its name?"
MATCH (lemma:Decl)<-[u:USES]-(:Decl)
WITH lemma, count(u) AS use_count
WHERE use_count = 1 AND lemma.kind IN ['theorem', 'def']
RETURN lemma.name, lemma.file, lemma.kind
ORDER BY lemma.file, lemma.name;
