@[expose] public section

open scoped BigOperators

namespace Hadamard

namespace OrderOne

open Real Hadamard.DyadicBounds

theorem ncard_zeros_le_rpow
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_finite : hasFiniteOrder f) (hf_order_le : order f ≤ 1)
    (Z : ZeroSet f)
    (h_zeros_only : ∀ s : ℂ, f s = 0 ↔ ∃ ρ : Z.Zero, s = Z.z ρ)
    (h_inj : Function.Injective Z.z)
    (h_z_ne_zero : ∀ ρ : Z.Zero, Z.z ρ ≠ 0)
    (h_simple : ∀ ρ : Z.Zero, deriv f (Z.z ρ) ≠ 0) :
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ C : ℝ, 0 ≤ C ∧
        ∀ r : ℝ, R₀ ≤ r →
          (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ) ≤ C * r ^ ((1 : ℝ) + ε) := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ :=
    ncard_zeros_le_of_order_le_one (f := f) hf_entire hf_finite hf_order_le Z h_zeros_only h_inj
      h_z_ne_zero h_simple ε hε
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let C : ℝ := ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2
  refine ⟨max R₁ 1, C, ?_, ?_⟩
  · have hC_nonneg : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
      have hpow : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      exact add_nonneg hpow (abs_nonneg _)
    exact div_nonneg hC_nonneg (le_of_lt hlog2_pos)
  intro r hr
  have hr_ge_R1 : R₁ ≤ r := le_trans (le_max_left _ _) hr
  have hr_ge1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr_nonneg : 0 ≤ r := le_trans (by norm_num : (0 : ℝ) ≤ 1) hr_ge1
  have hcount := hR₁ r hr_ge_R1
  -- First, replace `-log ‖f 0‖` by `|log ‖f 0‖|`.
  have hnum_le :
      (2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖
        ≤ (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
    have : -Real.log ‖f 0‖ ≤ |Real.log ‖f 0‖| := by
      simpa using (neg_le_abs (Real.log ‖f 0‖))
    linarith
  have hcount' :
      (({ρ : Z.Zero | ‖Z.z ρ‖ ≤ r} : Set Z.Zero).ncard : ℝ)
        ≤ ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2 := by
    have hfrac_le :
        ((2 * r) ^ ((1 : ℝ) + ε) - Real.log ‖f 0‖) / Real.log 2
          ≤ ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum_le (le_of_lt hlog2_pos)
    exact le_trans hcount hfrac_le
  -- Rewrite `(2*r)^(1+ε)` and absorb the constant using `r^(1+ε) ≥ 1`.
  have hrpow_ge1 : (1 : ℝ) ≤ r ^ ((1 : ℝ) + ε) :=
    Real.one_le_rpow hr_ge1 (by linarith [hε] : (0 : ℝ) ≤ (1 : ℝ) + ε)
  have hmul_rpow :
      (2 * r) ^ ((1 : ℝ) + ε)
        = (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) := by
    simpa using
      (Real.mul_rpow (x := (2 : ℝ)) (y := r) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) hr_nonneg
        (z := (1 : ℝ) + ε))
  have hnum2 :
      (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|
        ≤ ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) * r ^ ((1 : ℝ) + ε) := by
    have habs_mul : |Real.log ‖f 0‖| ≤ |Real.log ‖f 0‖| * r ^ ((1 : ℝ) + ε) :=
      le_mul_of_one_le_right (abs_nonneg _) hrpow_ge1
    calc
      (2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|
          = (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| := by
              simp [hmul_rpow]
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) + ε) * r ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖| * r ^ ((1 : ℝ) + ε) := by
              gcongr
      _ = ((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) * r ^ ((1 : ℝ) + ε) := by
              ring
  have hfrac2 :
      ((2 * r) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2
        ≤ (((2 : ℝ) ^ ((1 : ℝ) + ε) + |Real.log ‖f 0‖|) / Real.log 2) * r ^ ((1 : ℝ) + ε) := by
    have := div_le_div_of_nonneg_right hnum2 (le_of_lt hlog2_pos)
    simpa [div_mul_eq_mul_div, mul_assoc] using this
  have := le_trans hcount' hfrac2
  simpa [C, mul_assoc] using this

end OrderOne
end Hadamard
end
