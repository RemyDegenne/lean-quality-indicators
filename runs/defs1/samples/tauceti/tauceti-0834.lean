public section

open Finsupp

namespace MvPolynomial

variable {σ R : Type*} [LinearOrder σ] [WellFoundedGT σ]

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R} {a : σ → R} {v : σ →₀ ℕ}

/-- The Lazard valuation of `p` at `a`: the lexicographically least exponent of a nonzero
Taylor coefficient of `p` at `a`, and `⊤` if there is none. In the lexicographic order on
`Lex (σ →₀ ℕ)` the least variable is the most significant. -/
noncomputable def lazardValuation (p : MvPolynomial σ R) (a : σ → R) :
    WithTop (Lex (σ →₀ ℕ)) :=
  (taylor a p : MvPowerSeries σ R).lexOrder

end CommSemiring
end MvPolynomial
end
