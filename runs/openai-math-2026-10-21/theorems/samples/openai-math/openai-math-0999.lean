namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB3_1_4I2S2_0_2Entropy_sound : CB3_1_4I2S2_0_2Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2S2_0_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2S2_0_2Value CB3_1_4I2S2_0_2Terms CB3_1_4I2S2_0_2Terms_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
