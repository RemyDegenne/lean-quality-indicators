namespace P2MW.S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq

set_option autoImplicit false

p2m_open

universe u

namespace ISOAux

p2m_open

theorem comp_toSpecΓ {X : Scheme.{u}} (U : X.Opens) {R : CommRingCat.{u}} (g : Spec R ⟶ (U : Scheme.{u})) :
    g ≫ U.toSpecΓ = Spec.map (U.topIso.inv ≫ g.appTop ≫ (Scheme.ΓSpecIso R).hom) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

end ISOAux
end P2MW.S_AlgebraicGeometry_exists_iso_isoSpec_inv_comp_eq_of_specMap_comp_eq
