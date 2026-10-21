namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB4_3_1I2R16Raw_sound (a : Fin 6) :
    (CB4_3_1I2R16Raw a).Encloses (CB4_3_1I2R16Value a) := by
  exact residualBall_sound_on (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (stageBPriority (shape 4 3 1)) 2 (fun u => B4_3_1Little u ((stageBPriority (shape 4 3 1)) 2)) (fun u a => (littleLaw (shape 4 3 1) u ((stageBPriority (shape 4 3 1)) 2) a : ℝ)) (fun u _ => B4_3_1Law_sound u) (fun u _ a => B4_3_1Little_sound u ((stageBPriority (shape 4 3 1)) 2) a) 16 a

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
