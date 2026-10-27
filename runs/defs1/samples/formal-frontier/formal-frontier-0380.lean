open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

/-- A terminal exponent has no occupied pair separated by at least two indices;
equivalently no `outerExponent` fits inside it. -/
def Normal (n : ℕ) (d : Fin (n + 1) →₀ ℕ) : Prop :=
  ∀ p : MinorIndex n, ¬ outerExponent n p ≤ d

end
end
end ToricIdeals.RationalNormalCurve
