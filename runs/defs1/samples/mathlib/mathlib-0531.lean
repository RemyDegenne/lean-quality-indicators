@[expose] public section

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

attribute [local simp] map_mkPrecomp_eqToHom

/-- This is the functor `F ↦ X ↦ YonedaCollection F X`. -/
@[simps]
def yonedaCollectionFunctor (A : Cᵒᵖ ⥤ Type v) :
    ((CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ Type v where
  obj := yonedaCollectionPresheaf A
  map η := yonedaCollectionPresheafMap₁ η

end OverPresheafAux
end CategoryTheory
end
