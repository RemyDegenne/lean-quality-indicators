namespace P2MW.S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle

set_option autoImplicit false

p2m_open

namespace BiRigidify

noncomputable def unit_of_tensor_unit {X : Scheme.{0}} {N M : X.Modules} (d : N ⊗ M ≅ 𝟙_ _) (e : N ≅ 𝟙_ _) : M ≅ 𝟙_ _ :=
  (λ_ M).symm ≪≫ (e.symm ⊗ᵢ Iso.refl M) ≪≫ d

end BiRigidify
end P2MW.S_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
