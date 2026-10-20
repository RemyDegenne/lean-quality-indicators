@[expose] public section

open Module Polynomial

namespace IntermediateField

section AdjoinIntegralElement

universe u

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {α : E}

variable {K : Type u} [Field K] [Algebra F K]

theorem minpoly_gen (α : E) :
    minpoly F (AdjoinSimple.gen F α) = minpoly F α := by
  rw [← minpoly.algebraMap_eq (algebraMap F⟮α⟯ E).injective, AdjoinSimple.algebraMap_gen]

end AdjoinIntegralElement
end IntermediateField
end
