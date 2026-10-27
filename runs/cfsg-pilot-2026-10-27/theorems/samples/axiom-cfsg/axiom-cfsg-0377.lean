public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra

theorem s16h_e3_z3f5_cube_eq_zero_or_one (y : OmegaField) : y ^ 3 = 0 ∨ y ^ 3 = 1 := by
  obtain ⟨a, b, rfl⟩ := omegaField_eq y
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;>
    simp only [map_zero, map_one, zero_add, zero_mul, one_mul, add_zero]
  · left; simp
  · right; exact s16h_e3_z3f5_omega_cube
  · right; simp
  · right
    rw [add_comm, ← omega_sq, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul,
      s16h_e3_z3f5_omega_cube, one_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
