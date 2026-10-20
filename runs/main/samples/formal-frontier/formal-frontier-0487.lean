@[expose] public section

set_option warningAsError true

open scoped TrivSqZeroExt

namespace MvPolynomial

universe uK uι

section

theorem isOpen_reduced_atPrime_pointSquareZeroQuotient_iff_finite_range
    {K : Type uK} [Field K] {ι : Type uι} (a : ι → K)
    (ha : Function.Injective a) :
    IsOpen {p : PrimeSpectrum (MvPolynomial.pointSquareZeroQuotient a) |
      _root_.IsReduced (Localization.AtPrime p.asIdeal)} ↔
      (Set.range a).Finite := by
  have hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j) := by
    intro i j hij
    exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hij (ha h)))
  exact (PrimeSpectrum.isOpen_isReduced_atPrime_iff_ringEquiv
    (pointSquareZeroAlgEquiv a hsep).toRingEquiv).trans
      (Polynomial.isOpen_reduced_atPrime_directSum_evalQuotient_iff_finite_range a)

end
end MvPolynomial
end
