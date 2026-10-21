namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets.LinearNormalization

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_eval_cons_one_with_zero [Infinite K]
    (j : Fin n) {f : MvPolynomial (Fin (n + 1)) K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hnot : ¬ X j.succ ∣ f) :
    ∃ c : Fin n → K, c j = 0 ∧ eval (Fin.cons 1 c) f ≠ 0 := by
  have hne : aeval (Function.update (X (R := K)) j.succ 0) f ≠ 0 :=
    (WeightedTorusJets.Geometry.aeval_update_zero_eq_zero_iff j.succ f).not.mpr hnot
  obtain ⟨c, hc⟩ := exists_eval_cons_one_ne_zero
    (WeightedTorusJets.Geometry.isHomogeneous_aeval_update_zero j.succ hf) hne
  refine ⟨Function.update c j 0, Function.update_self j 0 c, ?_⟩
  have hvec : Function.update (Fin.cons 1 c : Fin (n + 1) → K) j.succ 0 =
      (Fin.cons 1 (Function.update c j 0) : Fin (n + 1) → K) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    | succ i => simp [Function.update_apply, Fin.succ_inj]
  rwa [eval_aeval_update_zero, hvec] at hc

end WeightedTorusJets.LinearNormalization
end SiegelZeros
end OAI
