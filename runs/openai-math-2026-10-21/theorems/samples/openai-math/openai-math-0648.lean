namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA1_5_10I2Singleton_sound : CA1_5_10I2Singleton.Encloses
    (singletonEntropy (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_5_10I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_5_10Law_sound u) CA1_5_10I2Singles_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
