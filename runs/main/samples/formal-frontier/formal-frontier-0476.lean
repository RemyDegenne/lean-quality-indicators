@[expose] public section

universe u v

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R]

section

variable (n : ℕ)

@[simp] theorem axisSection_C (r : R) :
    axisSection R n (Polynomial.C r) =
      Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.C r) := by
  simp only [axisSection, AlgHom.comp_apply, Polynomial.aeval_C,
    MvPolynomial.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk]

end
end ToricIdeals.RationalNormalCurve
end
