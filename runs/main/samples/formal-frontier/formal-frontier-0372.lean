@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [cat : Category.{v} C]

variable (E Q P : MorphismProperty C) [mult : P.IsMultiplicative] (S : C)

variable [h : ∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]

@[reassoc (attr := simp)]
lemma pullbackPairingSymmetry_hom_app_fst (A : E.Over P S) (B : Q.Over P S) :
    ((pullbackPairingSymmetry E Q P S).hom.app (A, B)).left ≫
        @pullback.fst C cat B.left A.left S B.hom A.hom
          (@hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)) =
      pullback.snd A.hom B.hom := by
  rw [pullbackPairingSymmetry_hom_app_left]
  exact pullbackSymmetry_hom_comp_fst A.hom B.hom

end CategoryTheory.MorphismProperty.Over
end
