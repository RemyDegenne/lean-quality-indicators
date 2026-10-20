namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace LinearMap

namespace FlatKerBC

p2m_open

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

variable {M₀ M₁ M₂ : Type u} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]

variable (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)

def theta [Module.Flat R A] : A ⊗[R] LinearMap.ker g ≃ₗ[A] LinearMap.ker (g.baseChange A) :=
  (LinearEquiv.ofInjective _ (subtype_baseChange_injective A g)).trans
    (LinearEquiv.ofEq _ _ (range_subtype_baseChange A g))

end FlatKerBC
end LinearMap
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
