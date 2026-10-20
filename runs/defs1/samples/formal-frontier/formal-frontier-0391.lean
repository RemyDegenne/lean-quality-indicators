@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty.Over

open Limits

variable {C : Type u} [cat : Category.{v} C]

variable (E Q P : MorphismProperty C) [mult : P.IsMultiplicative] (S : C)

variable [h : ∀ A : E.Over P S, ∀ B : Q.Over P S, HasPullback A.hom B.hom]

/-- Interchanging the two structured factors gives a natural isomorphism of
ordinary-over pullback pairings. Reverse pullback existence is derived pointwise
from the selected forward family; no horizontal condition is imposed on the
components. -/
noncomputable def pullbackPairingSymmetry :
    @pullbackPairing C cat E Q P mult S h ≅
      Prod.swap (E.Over P S) (Q.Over P S) ⋙
        @pullbackPairing C cat Q E P mult S
          (fun B A ↦ @hasPullback_symmetry
            C cat A.left B.left S A.hom B.hom (h A B)) := by
  letI : ∀ B : Q.Over P S, ∀ A : E.Over P S, HasPullback B.hom A.hom :=
    fun B A ↦ @hasPullback_symmetry C cat A.left B.left S A.hom B.hom (h A B)
  let e (A : E.Over P S × Q.Over P S) :
      (pullbackPairing E Q P S).obj A ≅
        (Prod.swap (E.Over P S) (Q.Over P S) ⋙ pullbackPairing Q E P S).obj A :=
    CategoryTheory.Over.isoMk (pullbackSymmetry A.1.hom A.2.hom) (by
      rcases A with ⟨A, B⟩
      have hs :
          (pullbackSymmetry A.hom B.hom).hom ≫
              (pullback.fst B.hom A.hom ≫ B.hom) =
            pullback.snd A.hom B.hom ≫ B.hom :=
        pullbackSymmetry_hom_comp_fst_assoc (f := A.hom) (g := B.hom) B.hom
      simpa only [Functor.comp_obj, Prod.swap_obj, pullbackPairing_obj_left,
        pullbackPairing_obj_hom] using
        hs.trans (pullback.condition (f := A.hom) (g := B.hom)).symm)
  refine NatIso.ofComponents e ?_
  rintro ⟨A₁, A₂⟩ ⟨B₁, B₂⟩ f
  have hA : (e (A₁, A₂)).hom.left = (pullbackSymmetry A₁.hom A₂.hom).hom := rfl
  have hB : (e (B₁, B₂)).hom.left = (pullbackSymmetry B₁.hom B₂.hom).hom := rfl
  have hn :
      pullback.map A₁.hom A₂.hom B₁.hom B₂.hom f.1.left f.2.left (𝟙 S)
          (by simpa using (Over.w f.1).symm) (by simpa using (Over.w f.2).symm) ≫
        (pullbackSymmetry B₁.hom B₂.hom).hom =
      (pullbackSymmetry A₁.hom A₂.hom).hom ≫
        pullback.map A₂.hom A₁.hom B₂.hom B₁.hom f.2.left f.1.left (𝟙 S)
          (by simpa using (Over.w f.2).symm) (by simpa using (Over.w f.1).symm) := by
    apply pullback.hom_ext (f := B₂.hom) (g := B₁.hom)
    · simp only [pullback.map, Category.assoc, pullbackSymmetry_hom_comp_fst,
        pullback.lift_snd, pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]
    · simp only [pullback.map, Category.assoc, pullbackSymmetry_hom_comp_snd,
        pullback.lift_fst, pullback.lift_snd, pullbackSymmetry_hom_comp_snd_assoc]
  apply CategoryTheory.Over.OverMorphism.ext
  simpa only [CategoryTheory.Over.comp_left, Functor.comp_map, Functor.comp_obj,
    Prod.swap_obj, Prod.swap_map, pullbackPairing_map_left, pullbackPairing_obj_left,
    hA, hB] using hn

end CategoryTheory.MorphismProperty.Over
end
