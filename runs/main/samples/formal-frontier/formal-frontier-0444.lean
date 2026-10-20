@[expose] public section

set_option warningAsError true

namespace MonomialOrder

variable {σ ι R : Type*} [CommRing R]

variable (I : Ideal R) [IsAdicComplete I R]

variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)

variable (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))

theorem coeff_restrictedDivisionRemainder_eq_zero
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (α : σ →₀ ℕ) (i : ι) (hi : m.degree (b i) ≤ α) :
    MvPowerSeries.coeff α
      ((restrictedDivisionRemainder I m b hb f :
        MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R) = 0 := by
  have hcoeff : ∀ n, Ideal.Quotient.mk (I ^ n)
      (MvPowerSeries.coeff α
        ((restrictedDivisionRemainder I m b hb f :
          MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R)) = 0 := by
    intro n
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
      (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective
      (MvPowerSeries.adicReduction I n f)
    have hlevel : MvPowerSeries.adicReduction I n
        (MvPowerSeries.polynomialToRestricted I p) = MvPowerSeries.adicReduction I n f := by
      simpa only [MvPowerSeries.adicReduction_polynomial] using hp
    have hzero : (m.linearDivisionRemainder b hb p).coeff α = 0 := by
      by_contra hne
      exact (m.linearDivision_remainder_support b hb p α
        (Finsupp.mem_support_iff.mpr hne) i) hi
    have hrem : MvPowerSeries.adicReduction I n (restrictedDivisionRemainder I m b hb f) =
        MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) (m.linearDivisionRemainder b hb p) := by
      rw [restrictedDivisionRemainder,
        MvPowerSeries.adicReduction_restrictedLinearExtension,
        ← MvPowerSeries.polynomialLinearMapMod_map, hp]
    have hc := congrArg (fun q : MvPolynomial σ (R ⧸ I ^ n) => q.coeff α) hrem
    simpa only [MvPowerSeries.coeff_adicReduction, MvPolynomial.coeff_map,
      hzero, map_zero] using hc
  have hfun := IsHausdorff.funext' I (f := fun _ : Unit =>
    MvPowerSeries.coeff α
      ((restrictedDivisionRemainder I m b hb f :
        MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) : MvPowerSeries σ R))
    (g := fun _ : Unit => (0 : R)) (by intro n _; simpa using hcoeff n)
  exact congrArg (fun h : Unit → R => h ()) hfun

end MonomialOrder
end
