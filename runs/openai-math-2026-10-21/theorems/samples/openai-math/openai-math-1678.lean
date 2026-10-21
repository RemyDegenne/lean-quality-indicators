namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA2_2_12I2R15H_sound : CA2_2_12I2R15H.Encloses (homogeneousEntropy CA2_2_12I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I2R15Value CA2_2_12I2R15MassTerm_sound CA2_2_12I2R15Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
