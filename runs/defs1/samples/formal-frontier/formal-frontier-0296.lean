@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

open scoped TensorProduct

/-- Scalar extension of the degree-`d` submodule of the full Hankel quotient.
The equivalence identifies the scalar-extended monomial basis with the basis
over the coefficient algebra, with the same indices for every `n` and `d`. -/
def quotientHomogeneousBaseChangeEquiv
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (n d : ℕ) :
    S ⊗[R] quotientHomogeneousSubmodule R n d ≃ₗ[S]
      quotientHomogeneousSubmodule S n d :=
  ((quotientHomogeneousBasis R n d).baseChange S).equiv
    (quotientHomogeneousBasis S n d) (Equiv.refl _)

end
end ToricIdeals.RationalNormalCurve
end
