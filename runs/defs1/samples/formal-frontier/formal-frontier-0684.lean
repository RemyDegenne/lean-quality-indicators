@[expose] public section

universe u v

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R]

section

variable (n : ℕ)

/-- Embed a univariate polynomial in the Hankel quotient by evaluating its
indeterminate at the first quotient coordinate. -/
noncomputable def axisSection :
    Polynomial R →ₐ[R] (Source R n ⧸ hankelIdeal R n) :=
  (Ideal.Quotient.mkₐ R (hankelIdeal R n)).comp
    (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)) : Source R n))

end
end ToricIdeals.RationalNormalCurve
end
