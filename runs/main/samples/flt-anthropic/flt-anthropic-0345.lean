namespace P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps

set_option autoImplicit false

open NumberField

namespace RATIOCOVER

open Matrix

variable {K : Type*} [Field K]

theorem exists_eq_smul_of_mem_center {c : GL (Fin 2) K} (hc : c ∈ Subgroup.center (GL (Fin 2) K)) :
    ∃ a : K, (c : Matrix (Fin 2) (Fin 2) K) = a • 1 := by
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  exact ⟨a, by rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end RATIOCOVER
end P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps
