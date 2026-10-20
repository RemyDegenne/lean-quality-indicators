namespace P2MW.S_TWLoc_frobenius_conj_mul_pow_inv_wild

set_option autoImplicit false

open IsLocalRing

namespace TWLoc

local notation3 "𝔾" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

local notation3 "ℚbar" => AlgebraicClosure ℚ

variable (P : ValuationSubring (AlgebraicClosure ℚ))

theorem r_one {z : ℚbar} (hz : z ≠ 0) : r P 1 (Subgroup.one_mem _) hz = 1 := by
  unfold r
  rw [← map_one (residue P)]
  congr 1
  apply Subtype.ext
  simp [hz]

end TWLoc
end P2MW.S_TWLoc_frobenius_conj_mul_pow_inv_wild
