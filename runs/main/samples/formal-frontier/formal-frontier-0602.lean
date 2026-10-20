public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

theorem adicPolynomialLevelEquiv_factorPow (I : Ideal R) {m n : ℕ}
    (hmn : m ≤ n)
    (x : MvPolynomial σ R ⧸
      (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n) :
    adicPolynomialLevelEquiv (σ := σ) I m
        (Ideal.Quotient.factorPow (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
          hmn x) =
      MvPolynomial.map (Ideal.Quotient.factorPow I hmn)
        (adicPolynomialLevelEquiv (σ := σ) I n x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk, adicPolynomialLevelEquiv_mk,
    MvPolynomial.map_map]
  apply MvPolynomial.ext
  intro index
  simp only [MvPolynomial.coeff_map, RingHom.comp_apply, Ideal.Quotient.factor_mk]

end MvPowerSeries
end
