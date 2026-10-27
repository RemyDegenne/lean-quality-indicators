namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_of_projPresentation_monoidalV2

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Surjective IsAffineHom.of_comp HasAffineProperty HasAffineProperty.iff_of_iSup_eq_top IsProper Scheme.Hom IsFinite Scheme.Hom.image_preimage_eq_opensRange_inf IsAffine Scheme.preimage_basicOpen Spec Scheme Scheme.mem_basicOpen'' Proj.mem_basicOpen Proj IsSeparated IsFinite.iff_isProper_and_isAffineHom isAffineOpen_top isAffineHom_diagonal_iff Proj.stalkIso' IsProper.of_comp Proj.isAffineOpen_basicOpen Proj.basicOpen IsAffineOpen Scheme.Modules Scheme.Hom.preimage_iSup Scheme.Opens Proj.iSup_basicOpen_eq_top Scheme.Hom.comp_preimage IsAffineHom Proj.awayToSection Scheme.Modules.map_smul Scheme.Opens.opensRange_ι ProjectiveSpectrum.Proj.awayToSection_germ Scheme.Modules.FiniteBySections ProjSpace.π ProjSpace.irrelevant_le_span_X ProjSpace.X_mem_one ProjSpace.ratio Scheme.Modules.tensorSections Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.IsFrameOn Scheme.Modules.IsFrameOn.tensorSections_monoidalV2 Scheme.Modules.exists_projPresentation_of_iSup_eq_top" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res basicOpen_of_isUnit Hom mk Γ Hom.image_preimage_eq_opensRange_inf preimage_basicOpen mem_basicOpen'' affineOpens basicOpen Modules Hom.preimage_iSup Opens Hom.comp_preimage Modules.map_smul Opens.opensRange_ι Modules.FiniteBySections Modules.tensorSections Modules.tensorSections_smul_left Modules.tensorSections_smul_right Modules.map_homOfLE_tensorSections Modules.IsFrameOn Modules.IsFrameOn.tensorSections_monoidalV2 Modules.exists_projPresentation_of_iSup_eq_top" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom map_smul ProjPresentation FiniteBySections tensorSections tensorSections_smul_left tensorSections_smul_right map_homOfLE_tensorSections IsFrameOn IsFrameOn.tensorSections_monoidalV2 exists_projPresentation_of_iSup_eq_top" namespace IsFrameOn p2m_export "AlgebraicGeometry.Scheme.Modules.IsFrameOn" "mono map tensorSections_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsFrameOn

set_option autoImplicit false

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

noncomputable section

namespace P2mSegreGG

section OnePresentation

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
  {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N)

abbrev DD (R : Type u) [CommRing R] (N : ℕ) (i : Fin (N + 1)) : (PP R N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)

end OnePresentation
end P2mSegreGG
end
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor_of_projPresentation_monoidalV2
