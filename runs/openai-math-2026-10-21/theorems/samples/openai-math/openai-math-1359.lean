namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB2_4_2I1PairP_sound (a : PairSlot) :
    (CB2_4_2I1PairP a).Encloses (CB2_4_2I1PairValue a) :=
  contains_sound (CB2_4_2I1PairRaw_sound a) (CB2_4_2I1PairP_check a)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
