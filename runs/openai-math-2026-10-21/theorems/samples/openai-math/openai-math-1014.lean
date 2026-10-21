namespace OAI

noncomputable section

open scoped BigOperators

namespace AtomicTriangular.FiniteCertificate

open Construction AtomicTriangular.Interval

lemma tr0_3_0_6_calc (r : Fin 8) : taylorRowBox 0 3 0 6 r = tr0_3_0_6 r := by
  revert r
  decide +kernel

end AtomicTriangular.FiniteCertificate
end
end OAI
