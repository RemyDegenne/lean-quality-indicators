public section

namespace TauCeti

open Finset MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}

/-- **The multiset of letters of a monomial** of total degree `n`, read as an element of
`Sym σ n`: the letter `x` occurs as often as the exponent of `x` prescribes. -/
noncomputable def weightSym (d : σ →₀ ℕ) (h : d.degree = n) : Sym σ n :=
  ⟨d.toMultiset, (card_toMultiset_eq_degree d).trans h⟩

end TauCeti
end
