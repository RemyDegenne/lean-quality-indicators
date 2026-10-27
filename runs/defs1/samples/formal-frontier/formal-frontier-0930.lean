@[expose] public section

universe u w

namespace MvPolynomial

/-- Separate the complementary variables from the variables in `S`, treating
polynomials in `S` as coefficients. -/
noncomputable def splitComplAlgEquiv {R : Type u} {τ : Type w}
    [CommSemiring R] (S : Set τ) :
    MvPolynomial τ R ≃ₐ[R] MvPolynomial (Sᶜ : Set τ) (MvPolynomial S R) := by
  classical
  exact (renameEquiv R ((Equiv.Set.sumCompl S).symm.trans
    (Equiv.sumComm S (Sᶜ : Set τ)))).trans (sumAlgEquiv R (Sᶜ : Set τ) S)

end MvPolynomial
end
