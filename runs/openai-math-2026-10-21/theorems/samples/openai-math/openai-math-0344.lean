namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB4_2_2I2R15Terms_sound (a : Fin 6) :
    (CB4_2_2I2R15Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I2R15Certificates_valid
    (CB4_2_2I2R15CertificateIndex a) (CB4_2_2I2R15P_sound a)

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
