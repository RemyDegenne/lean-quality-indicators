namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth

set_option autoImplicit false

open MvPolynomial CategoryTheory AlgebraicGeometry AlgebraicGeometry.HilbertFunctor

open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbRepGotz

variable {R₀ : Type} [CommRing R₀] {n : ℕ} {m : ℕ}

scoped instance instFiniteSm : Module.Finite R₀ (Sm R₀ n m) := finite_homogeneousSubmodule R₀ m

section IdealOf

variable (A : Type) [CommRing A] [Algebra R₀ A]

noncomputable def idealOf (N : Submodule A (A ⊗[R₀] Sm R₀ n m)) : Ideal (MvPolynomial (Fin (n + 1)) A) :=
  Ideal.span (formsOf A N : Set (MvPolynomial (Fin (n + 1)) A))

end IdealOf
end HilbRepGotz
end P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_scheme_represents_and_isClosedImmersion_toProjSpace_of_maximal_growth
