namespace OAI

section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem simplexTime_integral (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ s in Ioc 0 T, simplexTime n (T-s)) = simplexTime (n+1) T := by
  let f : ℝ → ℝ := fun s => (T-s)^n/(n.factorial : ℝ)
  have hi : IntegrableOn f (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((show Continuous f by dsimp [f]; fun_prop).intervalIntegrable 0 T)
  change (∫⁻ s in Ioc 0 T, ENNReal.ofReal (f s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← intervalIntegral.integral_of_le hT]
    change ENNReal.ofReal (∫ s in (0 : ℝ)..T, (T-s)^n/(n.factorial : ℝ)) = _
    rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n),
      integral_pow]
    simp only [sub_self,sub_zero,zero_pow (Nat.succ_ne_zero n),simplexTime,
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    congr 1
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hs.2) _) (Nat.cast_nonneg _)

end BoltzmannNonuniqueness.ReferenceGeometry
end
end
end OAI
