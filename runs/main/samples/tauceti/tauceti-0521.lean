public section

universe v₁ v₂ u₁ u₂

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace StableConflationExact

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]

variable {E : ExactStructure C} {E' : ExactStructure D}

variable {F : Functor C D} [F.Additive]

theorem isProjective_I_mapSuspensionPresentation (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    E'.isProjective (hF.mapSuspensionPresentation hE X).I :=
  ((E'.projectiveInjective_iff _).1 <| hF.map_projectiveInjective <|
    (E.projectiveInjective_iff _).2
      ⟨hE.isProjective_I (hE.suspensionPresentation X),
        (hE.suspensionPresentation X).isInjective⟩).1

end StableConflationExact
end TauCeti
end
