@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

section RowData

variable [∀ i, Ring (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

section

variable [Finite ι]

/-- The supported coefficient-product row is linearly equivalent to the
canonical row restricted along the opposite coordinate projection. The map
projects to the selected factor and uses the regular-row comparison; the inverse
inserts that row in the selected factor. The selected matrix index may be empty. -/
noncomputable def matrixBlockModuleLinearEquivRow (i : ι) :
    matrixBlockModule D κ i ≃ₗ[(∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ]
      (ModuleCat.restrictScalars
        (RingHom.op (Pi.evalRingHom (fun j ↦ Matrix (κ j) (κ j) (D j)) i))).obj
          (ModuleCat.of (Matrix (κ i) (κ i) (D i))ᵐᵒᵖ (κ i → D i)) := by
  classical
  let A := fun j ↦ Matrix (κ j) (κ j) (D j)
  let Mi := fun j ↦ (matrixRowFactors D κ i j).obj
  let p : (∀ j, A j)ᵐᵒᵖ →+* (A i)ᵐᵒᵖ := RingHom.op (Pi.evalRingHom A i)
  let row := ModuleCat.of (A i)ᵐᵒᵖ (κ i → D i)
  have hzero : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (Mi j) := by
    intro j hj
    change CategoryTheory.Limits.IsZero ((matrixRowFactors D κ i j).obj)
    rw [matrixRowFactors_of_ne D κ i j hj]
    exact ModuleCat.isZero_of_subsingleton _
  let e := (ModuleCat.FiniteProjective.piLinearEquiv A (matrixRowFactors D κ i)).trans
    (ModuleCat.piRightLinearEquivOfIsZero A Mi i hzero)
  let f : Mi i ≃ₗ[(A i)ᵐᵒᵖ] row :=
    (CategoryTheory.eqToIso (matrixRowFactors_same D κ i)).toLinearEquiv.trans
      (ModuleCat.toRightMatrixModCatRegularLinearEquiv (D i) (κ i))
  let erow : (ModuleCat.restrictScalars p).obj (Mi i) ≃ₗ[(∀ j, A j)ᵐᵒᵖ]
      (ModuleCat.restrictScalars p).obj row :=
    { toFun := f
      invFun := f.symm
      left_inv := f.symm_apply_apply
      right_inv := f.apply_symm_apply
      map_add' := f.map_add
      map_smul' := fun a x ↦ by
        change f (p a • x) = p a • f x
        exact f.map_smul (p a) x }
  exact e.trans erow

end
end RowData
end KTheory
end
