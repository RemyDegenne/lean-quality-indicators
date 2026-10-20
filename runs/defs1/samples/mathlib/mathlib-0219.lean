@[expose] public section

namespace CategoryTheory

open Category Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {A : Cᵒᵖ ⥤ Type v}

namespace OverPresheafAux

attribute [local simp] map_mkPrecomp_eqToHom

section counit

variable {F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v} {X : C}

/-- Backward direction of the counit. -/
def counitBackward (F : (CostructuredArrow yoneda A)ᵒᵖ ⥤ Type v)
    (s : CostructuredArrow yoneda A) :
    OverArrows (yonedaCollectionPresheafToA F) s.hom → F.obj (op s) :=
  fun p => F.map (eqToHom (by simp [← CostructuredArrow.eq_mk])) p.val.snd

end counit
end OverPresheafAux
end CategoryTheory
end
