namespace OAI

section

noncomputable section

open Filter Topology

namespace Nagata.W22

open Nagata.W21

theorem tendstoUniformlyOn_scaledThetaPositive
    {α : Type*} {l : Filter α} {τ : α → ℝ} {a R : ℝ} {δ : ℂ}
    (ha : 0 < a) (hδ : ‖δ‖ ≤ 1) (hR : 0 ≤ R)
    (hτ : Tendsto τ l (𝓝 0)) (hτpos : ∀ᶠ j in l, 0 < τ j) :
    TendstoUniformlyOn (fun j => scaledThetaPositive a δ (τ j)) (fun _ => 1)
      l {x : ℂ | ‖x‖ ≤ R} := by
  let u : α → ℕ → ℂ → ℂ := fun j t x =>
    -((τ j : ℂ) ^ t * (((τ j ^ a : ℝ) : ℂ) * Complex.exp (δ * x)))
  let B : α → ℝ := fun j => 2 * (τ j ^ a * Real.exp R)
  have hp := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.comp hτ
  have hB : Tendsto B l (𝓝 0) := by
    simpa only [B, Function.comp_def, Real.zero_rpow ha.ne', zero_mul, mul_zero] using
      (hp.mul_const (Real.exp R)).const_mul 2
  have hhalf : ∀ᶠ j in l, τ j < 1 / 2 := hτ.eventually (gt_mem_nhds (by norm_num))
  have hg : Summable (fun t : ℕ => (1 / 2 : ℝ) ^ t) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∀ᶠ j in l, ∀ x ∈ {x : ℂ | ‖x‖ ≤ R}, Summable (fun t => ‖u j t x‖) := by
    filter_upwards [hτpos, hhalf] with j hj hh x hx
    exact (hg.mul_right (τ j ^ a * Real.exp R)).of_nonneg_of_le (fun t => norm_nonneg _)
      (fun t => scaledThetaPositive_factor_norm_le hj.le hh.le hδ hR hx t)
  have hbound : ∀ᶠ j in l, ∀ x ∈ {x : ℂ | ‖x‖ ≤ R}, (∑' t, ‖u j t x‖) ≤ B j := by
    filter_upwards [hτpos, hhalf, hsum] with j hj hh hs x hx
    calc
      _ ≤ ∑' t : ℕ, (1 / 2 : ℝ) ^ t * (τ j ^ a * Real.exp R) :=
        (hs x hx).tsum_le_tsum
          (fun t => scaledThetaPositive_factor_norm_le hj.le hh.le hδ hR hx t)
          (hg.mul_right _)
      _ = B j := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num [B]
  have h := Nagata.W03.tendstoUniformlyOn_tprod_one_add_of_tsum_norm_le hB hsum hbound
  unfold scaledThetaPositive thetaPositive
  simpa only [u, sub_eq_add_neg] using h

end Nagata.W22
end
end
end OAI
