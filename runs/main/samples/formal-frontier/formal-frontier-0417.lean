open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem spectrum_irreducible [IsDomain k] (n : ℕ) (hn : 1 ≤ n) :
    IrreducibleSpace (PrimeSpectrum (Source k n ⧸ hankelIdeal k n)) := by
  let _ := quotient_isDomain k n hn
  infer_instance

end
end
end ToricIdeals.RationalNormalCurve
