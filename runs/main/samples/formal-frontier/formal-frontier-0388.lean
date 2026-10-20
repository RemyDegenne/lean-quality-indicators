@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]

variable (E P : MorphismProperty C) [P.IsMultiplicative]

variable {S S' : C} (f : S' ⟶ S)

variable [E.HasPullbacksAlong f] [E.IsStableUnderBaseChangeAlong f]

variable [(P ⊓ E).IsStableUnderBaseChange] [E.HasOfPostcompProperty E]

lemma pullbackOfIntersectionOfPostcomp_map_left_eq_lift {A B : E.Over P S} (g : A ⟶ B) :
    ((pullbackOfIntersectionOfPostcomp E P f).map g).left =
      pullback.lift (f := B.hom) (g := f)
        (pullback.fst A.hom f ≫ g.left) (pullback.snd A.hom f)
        (by simp only [Category.assoc, Over.w, pullback.condition]) := rfl

end CategoryTheory.MorphismProperty.Over
end
