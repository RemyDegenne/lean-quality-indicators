open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem hankelIdeal_isRadical_iff (R : Type u) [CommRing R] (n : ℕ) :
    (hankelIdeal R n).IsRadical ↔ IsReduced R := by
  exact (Ideal.isRadical_iff_quotient_reduced (hankelIdeal R n)).trans
    (quotient_isReduced_iff R n)

end
end
end ToricIdeals.RationalNormalCurve
