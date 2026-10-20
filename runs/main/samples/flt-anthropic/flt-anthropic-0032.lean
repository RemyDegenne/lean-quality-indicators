namespace P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

open scoped TensorProduct

open TensorProduct

namespace CHRAux

variable {A₀ A : Type*} [CommRing A₀] [CommRing A] [Algebra A₀ A]

variable {G : Type*} [Group G]

variable (σ : G →* (A ≃+* A))

section Main

variable [Fintype G] [DecidableEq G]

theorem Tr_fixed (g : G) (c : A) : σ g (Tr σ c) = Tr σ c := by
  simp only [Tr, map_sum, ← σ_mul_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

end Main
end CHRAux
end P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient
