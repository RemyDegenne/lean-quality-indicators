public section

open MeasureTheory Set Complex intervalIntegral

open scoped Real Interval

namespace TauCeti

variable {a b : ℝ}

theorem ae_eq_zero_of_forall_integral_mul_sin_eq_zero (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioc a b)))
    (h : ∀ k : ℕ, 0 < k → ∫ x in a..b, g x * Real.sin (k * π * (x - a) / (b - a)) = 0) :
    g =ᵐ[volume.restrict (Ioc a b)] 0 := by
  have hzero := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_left (by linarith : 2 * a - b ≤ a))
    (ae_eq_zero_of_forall_fourierCoeffOn_eq_zero _ (memLp_oddExtension hab hg)
      (fourierCoeffOn_oddExtension_eq_zero hab hg (integral_mul_sin_intCast_eq_zero h)))
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioc] with x hx hxm
  rw [Pi.zero_apply, oddExtension_of_lt hxm.1] at hx
  exact_mod_cast hx

end TauCeti
end
