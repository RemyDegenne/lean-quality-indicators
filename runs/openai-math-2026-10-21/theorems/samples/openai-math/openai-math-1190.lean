namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparation_step_caps (s n M R h He c : ℕ) {p δ : ℝ}
    (hp : 0 ≤ p) (hδ : 0 < δ) (hh : h + 1 ≤ s)
    (he : He ≤ preparationHeight p s) (hc : c ≤ M) :
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((n : ℝ) + 1) ^ (h + 1) * R * n * ((h + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    let ρ₀ := min 1 (δ / (preparationOscillationCap s n R p + 1))
    R * He ^ c ≤ preparationModulusCap s M R p ∧ 0 < ρ₀ ∧ ρ₀ ≤ ρ := by
  intro K ρ ρ₀
  have hheight := preparationHeight_pos hp s
  have hq : He ^ c ≤ preparationHeight p s ^ M :=
    (Nat.pow_le_pow_left he c).trans (Nat.pow_le_pow_right hheight hc)
  have hKnat : (h + 1 + 1) * (n + 1) ^ (h + 1) * R * n * (h + 1) * He ≤
      preparationOscillationCap s n R p := by
    unfold preparationOscillationCap
    gcongr
  have hK : K ≤ preparationOscillationCap s n R p := by
    dsimp only [K]
    exact_mod_cast hKnat
  refine ⟨Nat.mul_le_mul_left R hq, by dsimp [ρ₀]; positivity, ?_⟩
  apply min_le_min_left 1
  exact div_le_div_of_nonneg_left hδ.le (by dsimp [K]; positivity) (by linarith)

end Erdos3
end
end OAI
