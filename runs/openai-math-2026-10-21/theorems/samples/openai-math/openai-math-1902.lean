namespace OAI

namespace Ostmann

theorem historyLine_denominator_ne_zero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K) (hs : ∀ s ∈ steps, φ s.u ≠ 0) :
    φ (historyLine steps v w).denominator ≠ 0 :=
  polynomialAncestorRows_denominator_ne_zero steps φ hs

end Ostmann
end OAI
