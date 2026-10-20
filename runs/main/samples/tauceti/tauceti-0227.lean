public section

open Finset

namespace TauCeti

namespace SU2

variable (d : ℕ)

theorem sub_inv_mul_character_symPower_torusHom (z : Circle) :
    ((z : ℂ) - (z : ℂ)⁻¹) * (symPower d).character (torusHom z)
      = (z : ℂ) ^ (d + 1) - ((z : ℂ)⁻¹) ^ (d + 1) := by
  have hz : (z : ℂ) ≠ 0 := z.coe_ne_zero
  rw [character_symPower_torusHom_zpow, mul_sum]
  have key : ∀ i ∈ range (d + 1),
      ((z : ℂ) - (z : ℂ)⁻¹) * (z : ℂ) ^ (2 * (i : ℤ) - d)
        = (z : ℂ) ^ (2 * ((i + 1 : ℕ) : ℤ) - d - 1) - (z : ℂ) ^ (2 * (i : ℤ) - d - 1) := by
    intro i _
    have hsplit : (z : ℂ) - (z : ℂ)⁻¹ = (z : ℂ) ^ (1 : ℤ) - (z : ℂ) ^ (-1 : ℤ) := by
      simp
    rw [hsplit, sub_mul, ← zpow_add₀ hz, ← zpow_add₀ hz]
    congr 2 <;> push_cast <;> ring
  rw [sum_congr rfl key, sum_range_sub (fun j : ℕ => (z : ℂ) ^ (2 * (j : ℤ) - d - 1)) (d + 1),
    inv_pow, ← zpow_natCast (z : ℂ) (d + 1)]
  have hbot : (0 : ℤ) - (d : ℤ) - 1 = -((d : ℤ) + 1) := by ring
  have htop : 2 * ((d : ℤ) + 1) - (d : ℤ) - 1 = (d : ℤ) + 1 := by ring
  push_cast
  rw [hbot, zpow_neg, htop]

end SU2
end TauCeti
end
