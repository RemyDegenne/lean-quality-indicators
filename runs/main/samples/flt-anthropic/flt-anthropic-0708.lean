namespace P2MW.S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion

namespace QuatVal

variable {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]}

open QuaternionAlgebra

theorem nrd_add (x y : ℍ[ℚ_[p], a, b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, nrd_mk, trd_mk]
  ring

end QuatVal
end P2MW.S_QuaternionAlgebra_norm_nrd_add_le_max_of_forall_isUnit
