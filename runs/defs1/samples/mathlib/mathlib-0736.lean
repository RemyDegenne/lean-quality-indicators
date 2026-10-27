public section

open CategoryTheory

open CategoryTheory.Functor

namespace CategoryTheory.Limits

universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

section FilteredColimits

attribute [instance 100] PreservesFilteredColimitsOfSize.preserves_filtered_colimits

section Reflects

/-- `ReflectsFilteredColimitsOfSize.{w', w} F` means that whenever the image of a filtered cocone
under `F` is a colimit cocone, the original cocone was already a colimit. -/
@[univ_out_params, pp_with_univ]
class ReflectsFilteredColimitsOfSize (F : C ⥤ D) : Prop where
  reflects_filtered_colimits :
    ∀ (J : Type w) [Category.{w'} J] [IsFiltered J], ReflectsColimitsOfShape J F

end Reflects
end FilteredColimits
end CategoryTheory.Limits
end
