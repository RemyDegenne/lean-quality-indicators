open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

section

variable (k : Type u) [CommSemiring k]

/-- The polynomial semiring in `x₀, …, xₙ`. -/
abbrev Source (n : ℕ) := MvPolynomial (Fin (n + 1)) k

end
end
end
end ToricIdeals.RationalNormalCurve
