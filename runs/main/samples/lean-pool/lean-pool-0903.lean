@[expose] public section

namespace Lean4LPD.PauliString

open Finset

variable {n : ℕ}

theorem pauliNorm_layerStep_error_le_model_of_source_regime
    (layers : ℕ → List (PauliString n × ℝ)) (Γ : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) {ko kh m r : ℕ}
    (hΓ : 0 < Γ) (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((layers T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ layers T, IsSelfAdjoint g.1) {a α t : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ layers T, |Real.sin g.2| ≤ a)
    (hα : 0 < α) (ht : 0 ≤ t) (haA : a ≤ α * t / (r : ℝ))
    (hsteps : 8 * (Real.exp 1) ^ 2 * ((ko : ℝ) + kh - 1) * α * t ≤ (r : ℝ))
    (hadm : Admissible (r : ℝ) (m : ℝ) (Γ : ℝ)) (hm : 1 ≤ m) (hr : 5 ≤ r)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    pauliNorm (((layerBlockEnd layers Γ) ^ r) O -
        layerStepTraj layers Γ (rungWeight ko kh (m + 1)) O r) ≤
      decayBase (Γ : ℝ) (kh : ℝ) α t ^ (m + 1) *
        (Real.exp 1 * ((m : ℝ) + 1)) ^ ((ko : ℝ) / (kh - 1 : ℕ)) * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have hW : rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) 2 = (ko : ℝ) + kh - 1 := by
    rw [← rungWeight_cast_eq_rungW hkh (by decide : 1 ≤ 2)]
    simp only [rungWeight, Nat.reduceSub, one_mul, Nat.cast_add,
      Nat.cast_sub (by omega : 1 ≤ kh), Nat.cast_one]
    ring
  have hB := source_entry_inflation_le_one hkh1 hc
    (by exact_mod_cast (by omega : 0 < r)) haA
    (by simpa only [hW, mul_assoc] using hsteps)
  exact pauliNorm_layerStep_error_le_model layers Γ O hΓ hkh hL hherm ha hsin hα ht haA
    hB hadm hm hr hloc

end Lean4LPD.PauliString
end
