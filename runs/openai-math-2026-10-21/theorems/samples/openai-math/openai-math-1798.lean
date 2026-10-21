namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA1_3_12I2R1MassTerm_sound : CA1_3_12I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I2R1Value a))) :=
  entropyTerm_zero_ball (CA1_3_12I2R1Mass_sound)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
