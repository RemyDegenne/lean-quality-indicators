namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA3_5_8I2R11MassTerm_sound : CA3_5_8I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I2R11Value a))) :=
  entropyTerm_zero_ball (CA3_5_8I2R11Mass_sound)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
