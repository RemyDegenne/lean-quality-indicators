@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial Finset

variable {K : Type*} [Field K] {d : ℕ}

section Counting

/-- Blueprint F01: the finset of exponent vectors `α : Fin d →₀ ℕ` of total degree
`α.degree = ∑ i, α i` at most `t`, i.e. the exponents of the monomials spanning `P_{d,≤t}`. -/
def exponentsLE (d t : ℕ) : Finset (Fin d →₀ ℕ) :=
  (range (t + 1)).biUnion fun k ↦ (univ : Finset (Fin d)).finsuppAntidiag k

end Counting
end Nikodym.LowerBound
end
