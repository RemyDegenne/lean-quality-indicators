@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

open ofBifunctor

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]

namespace MonoidalCategory

open CategoryTheory.Functor

/-- The trifunctor `F ((- ⊗ -) ⊗ -)` -/
abbrev curriedTensorPostPost (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensor C) (curriedTensorPost F)

end MonoidalCategory
end CategoryTheory
end
