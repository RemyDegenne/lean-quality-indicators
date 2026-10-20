@[expose] public section

universe v₁ v₂ u₁ u₂

open Opposite

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.Functor

variable [Category.{v₁} C]

namespace NatIso

variable {D : Type u₂} [Category.{v₂} D]

variable {F G : C ⥤ D}

lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerRight α H) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerRight (NatIso.unop α) H.unop ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch

end NatIso
end CategoryTheory
end
