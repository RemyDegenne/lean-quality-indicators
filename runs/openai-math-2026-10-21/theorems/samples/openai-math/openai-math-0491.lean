namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA3_4_9I1R0MassTerm_sound : CA3_4_9I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I1R0Mass_sound) CA3_4_9I1R0MassTermLog_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
