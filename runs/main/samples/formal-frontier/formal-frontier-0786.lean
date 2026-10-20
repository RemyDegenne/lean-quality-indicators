@[expose] public section

universe uR uι uκ uD uM uN

namespace KTheory

variable {R : Type uR} [Ring R] {ι : Type uι}

variable (D : ι → Type uD) (κ : ι → Type uκ)

section RowData

variable [∀ i, Ring (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [Finite ι]

variable (e : R ≃+* ∀ i, Matrix (κ i) (κ i) (D i))

@[simp]
theorem matrixBlockModuleOfRingEquivLinearEquivRow_apply (i : ι)
    (x : matrixBlockModuleOfRingEquiv D κ e i) :
    (matrixBlockModuleOfRingEquivLinearEquivRow D κ (e := e) i).toFun x = x.down := rfl

end RowData
end KTheory
end
