namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB5_1_2I2R11P_check : ∀ a : Fin 6, contains (CB5_1_2I2R11Raw a) (CB5_1_2I2R11P a) = true := by
  decide +kernel

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
