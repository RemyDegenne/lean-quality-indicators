@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [Category.{v} C]

variable (E Q P : MorphismProperty C) [P.IsMultiplicative] (S : C)

variable [∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]

@[simp]
lemma pullbackPairing_obj (A : E.Over P S) (B : Q.Over P S) :
    (pullbackPairing E Q P S).obj (A, B) =
      CategoryTheory.Over.mk (pullback.fst A.hom B.hom ≫ A.hom) := rfl

end CategoryTheory.MorphismProperty.Over
end
