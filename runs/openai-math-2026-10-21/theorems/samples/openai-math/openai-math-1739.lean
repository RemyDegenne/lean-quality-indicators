namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB5_2_1I1R13Mass_sound : CB5_2_1I1R13Mass.Encloses (∑ a, CB5_2_1I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB5_2_1I1R13P CB5_2_1I1R13Value CB5_2_1I1R13P_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
