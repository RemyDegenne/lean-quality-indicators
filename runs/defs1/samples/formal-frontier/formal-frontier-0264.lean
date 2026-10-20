@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

section RowData

variable [∀ i, Ring (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The finite-projective factor family supported at block `i`: its `i`th
factor is the direct right row, and all other factors are zero modules. The
row action is supplied by `ModuleCat.toRightMatrixModCat`. -/
noncomputable def matrixRowFactors (i j : ι) :
    ModuleCat.FiniteProjective.{max uκ uD, max uκ uD}
      (Matrix (κ j) (κ j) (D j))ᵐᵒᵖ := by
  classical
  exact if j = i then
    ⟨(ModuleCat.toRightMatrixModCat.{uD, uκ, uD} (D j) (κ j)).obj
        (ModuleCat.of (D j)ᵐᵒᵖ (D j)),
      ModuleCat.isFiniteProjective_toRightMatrixModCat_obj.{uD, uκ, uD}
        (D j) (κ j) (ModuleCat.of (D j)ᵐᵒᵖ (D j))
        ⟨inferInstance, inferInstance⟩⟩
    else ModuleCat.FiniteProjective.of _ PUnit.{max uκ uD + 1}

end RowData
end KTheory
end
