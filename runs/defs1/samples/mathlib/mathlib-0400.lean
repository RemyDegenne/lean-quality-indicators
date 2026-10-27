@[expose] public section

namespace LieModule.Cohomology

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
def d₂₃ : twoCochain R L M →ₗ[R] L →ₗ[R] L →ₗ[R] L →ₗ[R] M where
  toFun a := {
    toFun x := {
      toFun y := {
        toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
        map_add' _ _ := by simp; abel
        map_smul' _ _ := by simp [smul_sub] }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; simp [smul_sub] }
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; simp [smul_sub] }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

end LieModule.Cohomology
end
