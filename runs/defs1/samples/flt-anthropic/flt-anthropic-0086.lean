namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace OmegaPull

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)

include hφ

def kdAb : (T0.pre gY d).presheaf ⟶ ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d)).val.presheaf where
  app U := AddCommGrpCat.ofHom (kdfun gY gX φ hφ d U.unop)
  naturality {U U'} i := by
    obtain ⟨U⟩ := U; obtain ⟨U'⟩ := U'
    ext1
    change L₁ gY gX φ hφ d i = L₂ gY gX φ hφ d i
    refine Λext d (fun r x hx => ?_) (fun m => ?_)
    · rw [L₁_smul, L₂_smul]; exact congrArg (_ • ·) hx
    · rw [L₁_ιMulti, L₂_ιMulti]

end Main
end OmegaPull
end
end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
