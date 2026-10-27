@[expose] public section

open Multiplicative

universe u v w

namespace AddEquiv

variable {A : Type u} {G : Type v} {σ : Type w} [CommSemiring A] [AddCommGroup G]

/-- Additive coordinates on a group induce an algebra equivalence from its
group algebra to the corresponding multivariable Laurent polynomial algebra. -/
noncomputable def monoidAlgebraMultiplicativeEquivMvLaurentPolynomial
    (e : G ≃+ (σ →₀ ℤ)) :
    MonoidAlgebra A (Multiplicative G) ≃ₐ[A] MvLaurentPolynomial σ A :=
  (AddMonoidAlgebra.toMultiplicativeAlgEquiv A A G).symm.trans
    (AddMonoidAlgebra.domCongr A A e)

end AddEquiv
end
