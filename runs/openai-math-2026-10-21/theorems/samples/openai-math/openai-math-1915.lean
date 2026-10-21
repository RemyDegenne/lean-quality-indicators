namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB4_3_1I1R3MassTermLog_sound : CB4_3_1I1R3MassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I1R3Mass_sound) (w := CB4_3_1I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
