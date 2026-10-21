namespace OAI

namespace CycleClique

open scoped SimpleGraph

theorem certificate_1907_valid : certificate_1907.Valid 16 8 (patternOrder [[],[],[1],[1,1,3]]) (patternClique [[],[],[1],[1,1,3]]) (patternEdges [[],[],[1],[1,1,3]]) (patternAmount [[],[],[1],[1,1,3]]) (patternEdgeCount [[],[],[1],[1,1,3]]) [] := certificate_1907_checked

end CycleClique
end OAI
