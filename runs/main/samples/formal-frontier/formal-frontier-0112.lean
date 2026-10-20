@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]

variable (E P : MorphismProperty C) [P.IsMultiplicative]

variable {S S' : C} (f : S' ⟶ S)

variable [E.HasPullbacksAlong f] [E.IsStableUnderBaseChangeAlong f]

variable [(P ⊓ E).IsStableUnderBaseChange] [E.HasOfPostcompProperty E]

@[simp]
lemma pullbackOfIntersectionOfPostcomp_obj_left (A : E.Over P S) :
    ((pullbackOfIntersectionOfPostcomp E P f).obj A).left = Limits.pullback A.hom f := rfl

end CategoryTheory.MorphismProperty.Over
end
