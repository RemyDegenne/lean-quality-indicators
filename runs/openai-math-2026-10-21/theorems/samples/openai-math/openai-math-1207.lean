namespace OAI

noncomputable section

open scoped BigOperators

namespace ContinuumCoulomb.CountertermEvaluation

theorem row_error (rho p : ℕ) (hrho : 0 < rho) {m : ℕ}
    (u : Fin m → ℚ×ℚ) (hu : Function.Injective u) (i : Fin m) :
    |(row rho p (u i) (List.ofFn u):ℝ)-
      localizedCounterterm (GaussianFrequency.frequency rho)
        (fun j => PlanarForcingProgram.position (u j)) i| ≤
      (m:ℝ)*2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
  rw [row_ofFn]
  simp only [Rat.cast_sum,localizedCounterterm,localizedOffsiteSum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j : Fin m, 2*(guard rho:ℝ)^3*((p:ℝ)+1)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : i=j
      · subst j
        simp only [offsite,squaredDistance_eq_zero,ite_true,Rat.cast_zero,zero_div,sub_self,abs_zero]
        positivity
      · have huij : u i ≠ u j := fun hij => h (hu hij)
        simpa only [offsite,squaredDistance_eq_zero,ite_eq_right huij,ite_eq_right h]
          using entry_error rho p hrho (u i) (u j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ContinuumCoulomb.CountertermEvaluation
end
end OAI
