namespace P2MW.S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

open scoped TensorProduct

namespace CHRAux

variable {A₀ A : Type*} [CommRing A₀] [CommRing A] [Algebra A₀ A]

variable {G : Type*} [Group G]

variable (σ : G →* (A ≃+* A))

section Main

variable [Fintype G] [DecidableEq G]

variable (A₀) in
noncomputable def cocoord (S : Finset (A × A)) : (S → A₀) →ₗ[A₀] A :=
  ∑ p : S, (LinearMap.toSpanSingleton A₀ A p.1.2).comp (LinearMap.proj p)

end Main
end CHRAux
end P2MW.S_AlgebraicGeometry_Scheme_isFinite_flat_etale_of_free_of_quotient
