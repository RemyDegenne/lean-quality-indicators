@[expose] public section

open Complex Polynomial Set

open scoped InnerProductSpace Interval Real

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The polynomial whose functional calculus is the normalized
divided-difference remainder contour. -/
noncomputable def crouzeixProductRemainderPolynomial
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range p.natDegree,
    Polynomial.monomial i
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        contourIntegral
          (fun z => star (Polynomial.eval z p) *
            (p /ₘ (Polynomial.X - Polynomial.C z)).coeff i)
          Omega.boundaryParam)

end
