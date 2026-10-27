namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback

set_option autoImplicit false

p2m_open

noncomputable section

namespace FBC

open AlgebraicGeometry.Scheme.Modules

section lociso

variable {S' : Type} [CommRing S'] {X Y Z : Scheme.{0}}

def pullbackCompCongr {φ : X ⟶ Y} {ψ : Y ⟶ Z} {χ : X ⟶ Z} (h : φ ≫ ψ = χ) (M : Z.Modules) :
    (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj M) ≅ (Scheme.Modules.pullback χ).obj M :=
  (pullbackComp φ ψ).app M ≪≫ (pullbackCongr h).app M

end lociso
end FBC
end
end P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_faces_pullback_cube_iff_of_isPullback
