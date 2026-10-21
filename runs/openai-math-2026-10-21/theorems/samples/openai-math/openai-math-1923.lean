namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem triangle_complete_9 : ∀ c : Fin 103,
    (edge 9).2 < c → SeedEncoding.indexedAdj (edge 9).1 c →
    SeedEncoding.indexedAdj (edge 9).2 c →
      triangle (triangleIndex 9 c) = ((edge 9).1,(edge 9).2,c) := by decide +kernel

end EilenbergGanea.SeedChainCertificate
end
end OAI
