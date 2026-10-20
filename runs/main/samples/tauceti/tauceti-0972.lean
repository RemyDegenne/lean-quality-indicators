public section

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

theorem geodesicReflection_apply_eq_smul (g : PSL(2, ℝ)) (z : ℍ) :
    geodesicReflection g z =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL g * Matrix.ProjGenLinGroup.mk J *
        (Matrix.ProjectiveSpecialLinearGroup.toPGL g)⁻¹) • z := by
  rw [mul_smul, mul_smul, ← map_inv, toPGL_smul, pglMk_smul, toPGL_smul, geodesicReflection_apply,
    imaginaryAxisReflection_apply]

end TauCeti.UpperHalfPlane
end
end
