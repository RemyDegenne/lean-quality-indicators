namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA1_1_14I2R4Mass_sound : CA1_1_14I2R4Mass.Encloses (∑ a, CA1_1_14I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_1_14I2R4P CA1_1_14I2R4Value CA1_1_14I2R4P_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
