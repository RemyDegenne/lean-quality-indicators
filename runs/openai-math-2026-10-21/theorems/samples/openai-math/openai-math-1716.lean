namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA5_5_6I2R6MassTermLog_sound : CA5_5_6I2R6MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R6Mass_sound) (w := CA5_5_6I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
