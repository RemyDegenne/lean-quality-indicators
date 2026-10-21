namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem triangle_complete_297 : ∀ c : Fin 103,
    (edge 297).2 < c → SeedEncoding.indexedAdj (edge 297).1 c →
    SeedEncoding.indexedAdj (edge 297).2 c →
      triangle (triangleIndex 297 c) = ((edge 297).1,(edge 297).2,c) := by decide +kernel

end EilenbergGanea.SeedChainCertificate
end
end OAI
