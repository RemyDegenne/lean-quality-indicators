@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable {S}

variable (S)

variable (S₁ S₂)

variable {S₁ S₂}

variable {S}

section

variable (C)

variable [HasKernels C] [HasCokernels C]

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `S.cycles ⟶ S.X₂` for all short complexes `S`. -/
@[simps]
noncomputable def iCyclesNatTrans : cyclesFunctor C ⟶ ShortComplex.π₂ where
  app S := S.iCycles

end
end ShortComplex
end CategoryTheory
end
