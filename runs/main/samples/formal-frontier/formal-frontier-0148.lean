@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

variable [∀ i, DivisionRing (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Nonempty (κ i)] [Finite ι]

theorem matrixBlockModule_class (i : ι) :
    ProjectiveClass.of (∀ j, Matrix (κ j) (κ j) (D j))
        (matrixBlockModule D κ i) = ProjectiveClass.matrixFamilyRowClass D κ i := by
  classical
  rw [ProjectiveClass.matrixFamilyRowClass_eq,
    ProjectiveClass.matrixFamilyEquiv_symm_apply]
  change ProjectiveClass.of (∀ j, Matrix (κ j) (κ j) (D j))
    (ModuleCat.FiniteProjective.pi (fun j ↦ Matrix (κ j) (κ j) (D j))
      (matrixRowFactors D κ i)) = _
  rw [← ProjectiveClass.piEquiv_symm_of_module]
  apply congrArg
    (ProjectiveClass.piEquiv (fun j ↦ Matrix (κ j) (κ j) (D j))).symm
  funext j
  by_cases h : j = i
  · subst j
    rw [Pi.single_eq_same, ProjectiveClass.finrankEquiv_symm_one]
    have hregular : ProjectiveClass.of (D i) (D i) =
        ProjectiveClass.of (D i) (D i)ᵐᵒᵖ :=
      ProjectiveClass.of_eq_of_equiv (D i) (D i)
        (MulOpposite.opLinearEquiv (D i)ᵐᵒᵖ)
    have hfactor : matrixRowFactors D κ i i =
        ⟨(ModuleCat.toRightMatrixModCat.{uD, uκ, uD} (D i) (κ i)).obj
            (ModuleCat.of (D i)ᵐᵒᵖ (D i)),
          ModuleCat.isFiniteProjective_toRightMatrixModCat_obj.{uD, uκ, uD}
            (D i) (κ i) (ModuleCat.of (D i)ᵐᵒᵖ (D i))
            ⟨inferInstance, inferInstance⟩⟩ := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      exact matrixRowFactors_same D κ i
    rw [hfactor]
    exact (ProjectiveClass.matrixEquiv_of_module (D i) (κ i) (D i)).symm.trans
      (congrArg (ProjectiveClass.matrixEquiv (D i) (κ i)) hregular)
  · rw [matrixRowFactors_of_ne D κ i j h]
    simp only [ProjectiveClass.of_zero, Pi.single_eq_of_ne h, map_zero]

end KTheory
end
