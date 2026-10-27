public section

namespace CFSG.ClassicalInvolution.Q3

open Polynomial

section Eval

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem eq_zero_of_evalAt_eq_zero (S : Finset k) (h : Polynomial (Module.End k V))
    (hdeg : h.natDegree < S.card) (h0 : ∀ c ∈ S, evalAt c h = 0) : h = 0 := by
  have hco : ∀ i v (φ : Module.Dual k V), φ ((h.coeff i) v) = 0 := by
    intro i v φ
    set Q : k[X] := ∑ j ∈ Finset.range (h.natDegree + 1), C (φ ((h.coeff j) v)) * X ^ j with hQ
    have hev : ∀ c, Q.eval c = φ ((evalAt c h) v) := by
      intro c
      rw [hQ, Polynomial.eval_finsetSum, evalAt, Polynomial.eval₂_eq_sum_range]
      simp only [LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        RingHom.id_apply, Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply,
        map_smul, map_smul, smul_eq_mul, mul_comm]
    have hQdeg : Q.natDegree < S.card := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_) hdeg
      exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have hQ0 : Q = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q S
        (fun c hc => by rw [hev, h0 c hc]; simp) hQdeg
    by_cases hi : i ≤ h.natDegree
    · have hc := congrArg (fun p : k[X] => p.coeff i) hQ0
      simp only [hQ, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at hc
      rw [Finset.sum_eq_single i] at hc
      · simpa using hc
      · intro j _ hji
        simp [Ne.symm hji]
      · intro hi'
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)) hi'
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]
      simp
  refine Polynomial.ext fun i => ?_
  rw [Polynomial.coeff_zero]
  refine LinearMap.ext fun v => ?_
  exact (Module.forall_dual_apply_eq_zero_iff k _).mp (fun φ => hco i v φ)

end Eval
end CFSG.ClassicalInvolution.Q3
end
