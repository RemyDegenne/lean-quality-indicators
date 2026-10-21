namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB6_1_1I1R9Entropy_sound : CB6_1_1I1R9Entropy.Encloses (Foundation.finiteEntropy CB6_1_1I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB6_1_1I1R9Value CB6_1_1I1R9Terms CB6_1_1I1R9Terms_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
