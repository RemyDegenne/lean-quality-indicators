namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CA5_5_6I1PairP_check_5_2 : ∀ k l : Fin 6, contains (CA5_5_6I1PairRaw ((5,2),(k,l))) (CA5_5_6I1PairP ((5,2),(k,l))) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
