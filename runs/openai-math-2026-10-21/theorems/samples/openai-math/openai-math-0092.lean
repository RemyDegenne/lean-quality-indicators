namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea.SeedChainCertificate

theorem h1_boundary_cert_246 : ∀ j : Fin 270,
    h1Coeff (triangleEdges 246).1 j - h1Coeff (triangleEdges 246).2.1 j +
      h1Coeff (triangleEdges 246).2.2 j = if j = 246 then 1 else 0 := by decide +kernel

end EilenbergGanea.SeedChainCertificate
end
end OAI
