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

def kd : gY.topDifferentials d ⟶ (Scheme.Modules.pushforward φ).obj (gX.topDifferentials d) :=
  ((adjY (Y := Y)).homEquiv (T0.pre gY d) ((Scheme.Modules.pushforward φ).obj (gX.topDifferentials d))).symm
    (kdpre gY gX φ hφ d)

end Main
end OmegaPull
end
end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq
