@[expose] public section

noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

section

variable [HasZeroMorphisms V]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[implicit_reducible, simps]
protected def op (X : HomologicalComplex V c) : HomologicalComplex Vᵒᵖ c.symm where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

end
end HomologicalComplex
end
end
