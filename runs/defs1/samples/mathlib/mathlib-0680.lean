@[expose] public section

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

attribute [local simp] map_mkPrecomp_eqToHom

namespace YonedaCollection

variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}

/-- Functoriality of `YonedaCollection F X` in `X`. -/
def map₂ (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v) {Y : C} (f : X ⟶ Y)
    (p : YonedaCollection F Y) : YonedaCollection F X :=
  YonedaCollection.mk (yoneda.map f ≫ p.fst) <| F.map (CostructuredArrow.mkPrecomp p.fst f).op p.snd

end YonedaCollection
end OverPresheafAux
end CategoryTheory
end
