open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

/-- Weighted index sum `∑ i, i*d_i` of a source monomial. -/
def sourceWeight (n : ℕ) : (Fin (n + 1) →₀ ℕ) →+ ℕ :=
  Finsupp.weight (fun i : Fin (n + 1) ↦ i.val)

end
end
end ToricIdeals.RationalNormalCurve
