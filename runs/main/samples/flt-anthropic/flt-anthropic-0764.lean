namespace P2MW.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.Converse

open LanglandsTunnell

noncomputable section

namespace K9D

open Real LanglandsTunnell.Converse.ArchR

theorem exp_neg_le_factorial_mul_inv_pow (k : ℕ) {x : ℝ} (hx : 0 < x) :
    rexp (-x) ≤ (k.factorial : ℝ) * (x ^ k)⁻¹ := by
  have h : x ^ k / k.factorial ≤ rexp x := Real.pow_div_factorial_le_exp x hx.le k
  have hk : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hxk : 0 < x ^ k := pow_pos hx k
  have h2 : x ^ k ≤ k.factorial * rexp x := (div_le_iff₀' hk).1 h
  calc rexp (-x) = (x ^ k)⁻¹ * (x ^ k * rexp (-x)) := by field_simp
    _ ≤ (x ^ k)⁻¹ * (k.factorial * rexp x * rexp (-x)) := by gcongr
    _ = (k.factorial : ℝ) * (x ^ k)⁻¹ := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one, mul_comm]

end K9D
end
end P2MW.S_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand
