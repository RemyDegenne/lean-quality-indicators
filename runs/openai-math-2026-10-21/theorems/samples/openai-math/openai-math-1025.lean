namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem transfer_common_row_norm_one {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y : Y)
    (P : ZMod p) (U : Y → ZMod p) (hP : IsUnit P)
    (hU : ∀ z, z ≠ y → IsUnit (U z)) (hb : b (some (.inr y)) (some (.inr y)) = 0) :
    ‖χ P ^ b (some (.inr y)) none *
      ∏ z, χ (U z) ^ b (some (.inr y)) (some (.inr z))‖ = 1 := by
  classical
  obtain ⟨u, hu⟩ := hP
  rw [norm_mul, ← hu, norm_zpow, χ.unit_norm_eq_one, one_zpow, one_mul, norm_prod]
  apply Finset.prod_eq_one
  intro z _
  by_cases hz : z = y
  · subst z
    rw [hb, zpow_zero, norm_one]
  · obtain ⟨a, ha⟩ := hU z hz
    rw [← ha, norm_zpow, χ.unit_norm_eq_one, one_zpow]

end Ostmann
end OAI
