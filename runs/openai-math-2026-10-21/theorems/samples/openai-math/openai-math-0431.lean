namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA3_4_9I1R16P_check : ∀ a : PairSlot, contains (CA3_4_9I1R16Raw a) (CA3_4_9I1R16P a) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
