namespace OAI

noncomputable section

open scoped BigOperators

namespace AtomicTriangular.FiniteCertificate

open Construction AtomicTriangular.Interval Complex

lemma taylorExp0_0_12_mem (j : Fin 31) : (taylorExp0_0_12 j).Mem (exp (taylorPhase 0 0 (frequency j)*((12:ℤ):ℂ))) := by
  rw [← taylorExp0_0_12_calc]
  exact CI.mem_exp_checked (CI.mem_mul (taylorPhase0_0_mem j) (CI.mem_point 12)) (by
    revert j
    decide +kernel)

end AtomicTriangular.FiniteCertificate
end
end OAI
