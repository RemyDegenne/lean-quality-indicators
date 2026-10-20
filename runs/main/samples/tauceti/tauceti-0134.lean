public section

open scoped MatrixGroups

namespace Matrix.ProjectiveSpecialLinearGroup

variable {R : Type*} [CommRing R]

variable [NoZeroDivisors R]

@[simp]
theorem isParabolic_inv_iff {g : PSL(2, R)} : IsParabolic g⁻¹ ↔ IsParabolic g := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [← QuotientGroup.mk_inv, isParabolic_mk_iff, isParabolic_mk_iff]
  have hscalar (m : Matrix (Fin 2) (Fin 2) R) :
      m ∈ Set.range (scalar (Fin 2)) ↔ m 0 1 = 0 ∧ m 1 0 = 0 ∧ m 0 0 = m 1 1 := by
    refine ⟨by rintro ⟨r, rfl⟩; simp, fun ⟨h01, h10, h00⟩ ↦ ⟨m 0 0, ?_⟩⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00]
  simp only [GeneralLinearGroup.IsParabolic, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_inv, Matrix.IsParabolic, hscalar, Matrix.discr_fin_two,
    Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [eq_comm, and_comm, add_comm, mul_comm]

end Matrix.ProjectiveSpecialLinearGroup
end
