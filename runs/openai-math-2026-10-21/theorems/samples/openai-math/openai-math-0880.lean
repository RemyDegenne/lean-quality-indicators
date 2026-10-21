namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA1_7_8I2R5H_sound : CA1_7_8I2R5H.Encloses (homogeneousEntropy CA1_7_8I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I2R5Value CA1_7_8I2R5MassTerm_sound CA1_7_8I2R5Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
