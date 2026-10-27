namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom

set_option autoImplicit false

universe u

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

p2m_open

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "mapPresheaf app" end Hom

p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

section bridge

variable {A : Type u} [CommRing A] (A' : Type u) [CommRing A'] [Algebra A A']

noncomputable def restrictScalarsSelfEquiv :
    A' ≃ₗ[A'] ((ModuleCat.restrictScalars (CommRingCat.ofHom (algebraMap A A')).hom).obj (ModuleCat.of A' A')) :=
  LinearEquiv.refl A' A'

end bridge
end Hom
end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
