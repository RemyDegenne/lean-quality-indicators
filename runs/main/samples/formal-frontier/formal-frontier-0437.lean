open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem minor_mem (n : ℕ) (p : MinorIndex n) :
    hankelMinor k n p ∈ hankelIdeal k n := by
  apply Ideal.subset_span
  exact Set.mem_range_self p

end
end
end ToricIdeals.RationalNormalCurve
