@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]

variable (E P : MorphismProperty C) [P.IsMultiplicative]

variable {S S' : C} (f : S' ⟶ S)

variable [E.HasPullbacksAlong f] [E.IsStableUnderBaseChangeAlong f]

variable [(P ⊓ E).IsStableUnderBaseChange] [E.HasOfPostcompProperty E]

lemma pullbackOfIntersectionOfPostcomp_map_unique {A B : E.Over P S} (g : A ⟶ B)
    (k : (pullbackOfIntersectionOfPostcomp E P f).obj A ⟶
      (pullbackOfIntersectionOfPostcomp E P f).obj B)
    (hfst : k.left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left)
    (hsnd : k.left ≫ pullback.snd B.hom f = pullback.snd A.hom f) :
    k = (pullbackOfIntersectionOfPostcomp E P f).map g := by
  apply Over.Hom.ext
  apply pullback.hom_ext
  · exact hfst.trans (pullbackOfIntersectionOfPostcomp_map_fst E P f g).symm
  · exact hsnd.trans (pullbackOfIntersectionOfPostcomp_map_snd E P f g).symm

end CategoryTheory.MorphismProperty.Over
end
