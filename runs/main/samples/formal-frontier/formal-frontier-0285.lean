public section

set_option warningAsError true

namespace MvPowerSeries

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    (n : ℕ) (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V)

theorem existsUnique_firstVariable_division_of_scalar_top
    [IsAdicComplete (Ideal.span {a} : Ideal V) V]
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)
    (d : ℕ) (c : V ⧸ IsLocalRing.maximalIdeal V)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c) (hc : c ≠ 0)
    (h : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a})) :
    ∃! qr : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}) ×
        Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a})),
      h = qr.1 * f + polynomialRestrictedFinFirst (Ideal.span {a}) n qr.2 ∧
        qr.2.degree < (d : WithBot ℕ) := by
  exact existsUnique_firstVariable_division_of_leadingExponent n a ham ha hrad f hprim d
    (restrictedLeadingExponent_lex_eq_cons_of_scalar_top n a ham f hprim d c
      hdegree htop hc) h

end MvPowerSeries
end
