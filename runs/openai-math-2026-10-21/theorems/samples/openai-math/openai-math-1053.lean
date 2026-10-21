namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA1_6_9I2PairP_check_0_0 : ∀ k l : Fin 6, contains (CA1_6_9I2PairRaw ((0,0),(k,l))) (CA1_6_9I2PairP ((0,0),(k,l))) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
