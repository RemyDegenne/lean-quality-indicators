public section

noncomputable section

open Multiplicative

namespace TauCeti.OreExtension

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R] {σ : R →ₐ[k] R}
  [MulSemiringAction (Multiplicative ℕ) R]

variable (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a)

/-- An Ore extension with zero skew derivation is isomorphic, as a `k`-algebra, to Mathlib's skew
polynomial ring, for any action of `Multiplicative ℕ` commuting with the scalars `k` whose
generator acts by `σ`. -/
def skewPolynomialAlgEquiv [SMulCommClass (Multiplicative ℕ) k R] :
    OreExtension σ 0 ≃ₐ[k] SkewPolynomial R where
  __ := skewPolynomialEquiv hσ
  commutes' c := by
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, algebraMap_apply,
      skewPolynomialEquiv_C, SkewMonoidAlgebra.coe_algebraMap, Function.comp_apply]
    rw [← SkewPolynomial.monomial_zero_left, SkewPolynomial.monomial_def, ofAdd_zero]

end TauCeti.OreExtension
end
end
