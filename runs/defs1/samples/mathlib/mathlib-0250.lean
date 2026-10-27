@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ C₁₂ C₂₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₁₂] [Category* C₂₃]

section bifunctorComp₂₃Functor

/-- The functor `(C₁ ⥤ C₂₃ ⥤ C₄) ⥤ (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄` which
sends `F : C₁ ⥤ C₂₃ ⥤ C₄` and `G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃` to the
functor `bifunctorComp₂₃ F G₂₃ : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄`. -/
@[simps, implicit_reducible]
def bifunctorComp₂₃Functor :
    (C₁ ⥤ C₂₃ ⥤ C₄) ⥤ (C₂ ⥤ C₃ ⥤ C₂₃) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ where
  obj := bifunctorComp₂₃FunctorObj
  map := bifunctorComp₂₃FunctorMap

end bifunctorComp₂₃Functor
end CategoryTheory
end
