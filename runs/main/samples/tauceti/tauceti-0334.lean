public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

variable {R : Type*} [CommRing R]

variable [NoZeroDivisors R]

@[simp]
theorem isParabolic_upperRightHom_iff {x : R} : IsParabolic (upperRightHom x) ↔ x ≠ 0 := by
  rw [upperRightHom_apply, isParabolic_mk_iff, GeneralLinearGroup.IsParabolic,
    SpecialLinearGroup.coe_GL_coe_matrix, Matrix.isParabolic_iff_of_upperTriangular] <;>
    simp [SpecialLinearGroup.transvection_coe]

end Matrix.ProjectiveSpecialLinearGroup
end
