namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB2_3_3I2R11Terms_sound (a : Fin 6) :
    (CB2_3_3I2R11Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I2R11Certificates_valid
    (CB2_3_3I2R11CertificateIndex a) (CB2_3_3I2R11P_sound a)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
