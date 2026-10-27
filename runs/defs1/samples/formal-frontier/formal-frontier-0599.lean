@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]

variable (E P : MorphismProperty C) [P.IsMultiplicative]

variable {S S' : C} (f : S' ⟶ S)

variable [E.HasPullbacksAlong f] [E.IsStableUnderBaseChangeAlong f]

variable [(P ⊓ E).IsStableUnderBaseChange] [E.HasOfPostcompProperty E]

/-- When pullbacks along `f` exist for every over-object, forgetting structured
transport agrees with the ordinary over-category pullback functor. -/
@[simps! hom_app_left inv_app_left]
noncomputable def pullbackOfIntersectionOfPostcompCompForgetIso
    [Limits.HasPullbacksAlong f] :
    pullbackOfIntersectionOfPostcomp E P f ⋙ Over.forget E P S' ≅
      Over.forget E P S ⋙ CategoryTheory.Over.pullback f :=
  eqToIso (pullbackOfIntersectionOfPostcomp_comp_forget E P f) ≪≫
    Functor.isoWhiskerLeft (Over.changeProp S (P := E) (Q := P) le_rfl le_top)
      (Over.pullbackCompForgetIso (P := E) (Q := ⊤) f)

end CategoryTheory.MorphismProperty.Over
end
