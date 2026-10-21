namespace OAI

section

section

open MeasureTheory Set

open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

namespace Coulomb

theorem kinetic_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, kinetic (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      kinetic ψ + (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖ ^ 2 := by
  classical
  let χ := fun i => ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)
  have hblock : ∀ s a, (∑ i, ∫ x, ‖(χ i).gradient s a x‖ ^ 2) =
      (∫ x, ‖ψ.gradient s a x‖ ^ 2) +
      ∫ x, (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
        ‖ψ.value s x‖ ^ 2 := by
    intro s a
    have hi : ∀ i, Integrable (fun x =>
        (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2 * ‖ψ.value s x‖ ^ 2)
        volume := by
      intro i
      have hL := memLp_two_real_mul (ψ.value_L2 s)
        (((hf i).continuous_fderiv (by simp)).clm_apply continuous_const) (hD i a)
      simpa only [norm_real_mul_sq] using hL.integrable_norm_pow (p := 2) (by decide)
    have herr : Integrable (fun x =>
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖ ^ 2) volume := by
      simp_rw [Finset.sum_mul]
      exact integrable_finsetSum _ (fun i _ => hi i)
    rw [← integral_finsetSum _ (fun i _ =>
      ((χ i).partial_L2 s a).integrable_norm_pow (p := 2) (by decide))]
    have heq : (fun x => ∑ i, ‖(χ i).gradient s a x‖ ^ 2) =
        fun x => ‖ψ.gradient s a x‖ ^ 2 +
          (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
            ‖ψ.value s x‖ ^ 2 := by
      funext x
      exact ims_pointwise f hf hpart x (EuclideanSpace.single a 1)
        (ψ.value s x) (ψ.gradient s a x)
    rw [heq, integral_add ((ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)) herr]
  change (∑ i, kinetic (χ i)) = _
  unfold kinetic
  rw [← Finset.mul_sum]
  have hswap : (∑ i, ∑ s, ∑ a, ∫ x, ‖(χ i).gradient s a x‖ ^ 2) =
      ∑ s, ∑ a, ∑ i, ∫ x, ‖(χ i).gradient s a x‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [hblock, Finset.sum_add_distrib]
  ring

end Coulomb
end
end
end OAI
