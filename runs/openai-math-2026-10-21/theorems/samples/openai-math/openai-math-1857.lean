namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB6_1_1I2Singleton_sound : CB6_1_1I2Singleton.Encloses
    (singletonEntropy (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2 (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 6 1 1)) B6_1_1Law (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (stageBPriority (shape 6 1 1)) 2
    CB6_1_1I2Singles (fun u a => (littleLaw (shape 6 1 1) u ((stageBPriority (shape 6 1 1)) 2) a : ℝ)) (fun u _ => B6_1_1Law_sound u) CB6_1_1I2Singles_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
