namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

noncomputable section

namespace MatrixMultiplication.NativeNumerics

open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay

open AllFieldInitialEntropyCertificate AllFieldNativeCapacity

open scoped BigOperators

lemma CB2_2_4I2R3Raw_sound (a : Fin 6) :
    (CB2_2_4I2R3Raw a).Encloses (CB2_2_4I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (stageBPriority (shape 2 2 4)) 2 (fun u => B2_2_4Little u ((stageBPriority (shape 2 2 4)) 2)) (fun u a => (littleLaw (shape 2 2 4) u ((stageBPriority (shape 2 2 4)) 2) a : ℝ)) (fun u _ => B2_2_4Law_sound u) (fun u _ a => B2_2_4Little_sound u ((stageBPriority (shape 2 2 4)) 2) a) 3 a

end MatrixMultiplication.NativeNumerics
end
end
end MatrixAllFields
end OAI
