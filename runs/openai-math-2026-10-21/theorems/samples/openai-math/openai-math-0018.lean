namespace OAI

namespace PlanarFalconer

open Set MeasureTheory

open scoped ENNReal

theorem uniform_suffix_coefficient_absorption {sig eps : ℝ}
    (hsig : 0 ≤ sig) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a lam : ℝ, 0 ≤ lam →
      2255*((2:ℝ)^N)^(a+2000*(lam+sig)+12*lam) ≤
        ((2:ℝ)^N)^(a+4000*(lam+sig)+eps) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed heps 2255
  refine ⟨N₀,?_⟩
  intro N hN a lam hlam
  calc
    _ ≤ ((2:ℝ)^N)^eps*((2:ℝ)^N)^(a+2000*(lam+sig)+12*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(eps+(a+2000*(lam+sig)+12*lam)) := by
      rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

end PlanarFalconer
end OAI
