namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem triangle_complete_101 : ∀ c : Fin 103,
    (edge 101).2 < c → SeedEncoding.indexedAdj (edge 101).1 c →
    SeedEncoding.indexedAdj (edge 101).2 c →
      triangle (triangleIndex 101 c) = ((edge 101).1,(edge 101).2,c) := by decide +kernel

end EilenbergGanea.SeedChainCertificate
end
end OAI
