@[expose] public section

universe uR uι uκ uD uM uN

namespace KTheory

variable {R : Type uR} [Ring R] {ι : Type uι}

variable (D : ι → Type uD) (κ : ι → Type uκ)

section RowData

variable [∀ i, Ring (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [Finite ι]

variable (e : R ≃+* ∀ i, Matrix (κ i) (κ i) (D i))

/-- The supported right row over `R`, obtained by restriction of scalars along
the chosen matrix decomposition. The carrier lift puts both scalar rings and
this module in one supported module-category universe. -/
noncomputable def matrixBlockModuleOfRingEquiv (i : ι) :
    ModuleCat.FiniteProjective.{uR, max uR (max uι (max uκ uD))} Rᵐᵒᵖ :=
  ⟨(ModuleCat.restrictScalars.{max uR (max uι (max uκ uD))} e.op.toRingHom).obj
      (ModuleCat.of.{max uR (max uι (max uκ uD))}
        (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
        (ULift.{uR} (matrixBlockModule D κ i))),
    ModuleCat.isFiniteProjective_of_equivalence.{max uι (max uκ uD), uR,
      max uR (max uι (max uκ uD)), max uι (max uκ uD)}
      (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ Rᵐᵒᵖ
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.op)
      (ModuleCat.of.{max uR (max uι (max uκ uD))}
        (∀ j, Matrix (κ j) (κ j) (D j))ᵐᵒᵖ
        (ULift.{uR} (matrixBlockModule D κ i)))
      ⟨inferInstance, inferInstance⟩⟩

end RowData
end KTheory
end
