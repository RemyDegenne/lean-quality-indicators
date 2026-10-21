namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA1_4_11I1R2H_sound : CA1_4_11I1R2H.Encloses (homogeneousEntropy CA1_4_11I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_4_11I1R2Value CA1_4_11I1R2MassTerm_sound CA1_4_11I1R2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
