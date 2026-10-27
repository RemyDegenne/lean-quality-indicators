namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three

set_option autoImplicit false

open scoped Quaternion

p2m_open

namespace RootPow

open AlgebraicGeometry.Scheme.Modules

variable {S : Type} [CommRing S] {X : Scheme.{0}}

noncomputable def pullbackTriple {Y : Scheme.{0}} (h : Y ⟶ X) (P : X.Modules) :
    (Scheme.Modules.pullback h).obj (P ⊗ P ⊗ P) ≅
      (Scheme.Modules.pullback h).obj P ⊗ ((Scheme.Modules.pullback h).obj P ⊗ (Scheme.Modules.pullback h).obj P) :=
  pullbackTensorObjIso h _ _ ≪≫ (Iso.refl _ ⊗ᵢ pullbackTensorObjIso h _ _)

end RootPow
end P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_hasPrincipalRoot_of_isCanonicalPolData_of_locIsoOnBase_tensor_three
