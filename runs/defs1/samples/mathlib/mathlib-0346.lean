@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]

variable (F : C ⥤ D) (G : D ⥤ E)

attribute [instance] Functor.IsIso.faithful Functor.IsIso.full

section

variable {C D : Type*} [Category* C] (e : D ≃ C)

namespace InducedCategory

/-- The isomorphism of categories between `InducedCategory C e` and `C` when
`e : D ≃ C` is a bijection. -/
@[simps, implicit_reducible]
def isoCat : IsoCat (InducedCategory C e) C where
  functor := inducedFunctor e
  inverse.obj X := e.symm X
  inverse.map f := { hom := eqToHom (by simp) ≫ f ≫ eqToHom (by simp) }
  unit_eq := Functor.ext (by simp) (by cat_disch)
  counit_eq := Functor.ext (by simp) (by cat_disch)

end InducedCategory
end
end CategoryTheory
end
