/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.SingletonDivision
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableRegrouping.Fin
public import MultivariatePolynomials.FirstVariableLex

public section

/-!
# Restricted division in the first variable

A scalar nonzero top coefficient of the first-variable residue determines the
first-priority maximum lexicographic leading monomial. Primitive singleton
division then gives a unique quotient and a polynomial remainder of degree
strictly below that top degree, including degree zero.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    (n : ℕ) (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V)

/-- For a primitive restricted series, the scalar top residue fixes its
intrinsic leading exponent in the first-priority maximum lex order. -/
theorem restrictedLeadingExponent_lex_eq_cons_of_scalar_top
    [IsHausdorff (Ideal.span {a} : Ideal V) V]
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)
    (d : ℕ) (c : V ⧸ IsLocalRing.maximalIdeal V)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c) (hc : c ≠ 0) :
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))).restrictedLeadingExponent
        a ham f = (0 : Fin n →₀ ℕ).cons d := by
  rw [MonomialOrder.restrictedLeadingExponent_eq_degree_of_primitive_reduction
    (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) a ham f hprim
      (restrictedResidue a ham f) (fun index => coeff_restrictedResidue a ham f index)]
  exact MonomialOrder.lex_degree_of_finSuccEquiv_scalar_top n d
    (restrictedResidue a ham f) c hdegree htop hc

/-- Singleton division and coefficientwise finite support give a unique
polynomial remainder; this lower-level form isolates the cone calculation. -/
theorem existsUnique_firstVariable_division_of_leadingExponent
    [IsAdicComplete (Ideal.span {a} : Ideal V) V]
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)
    (d : ℕ)
    (hleading : MonomialOrder.restrictedLeadingExponent
      (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) a ham f =
        (0 : Fin n →₀ ℕ).cons d)
    (h : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a})) :
    ∃! qr : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}) ×
        Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a})),
      h = qr.1 * f + polynomialRestrictedFinFirst (Ideal.span {a}) n qr.2 ∧
        qr.2.degree < (d : WithBot ℕ) := by
  classical
  let I : Ideal V := Ideal.span {a}
  obtain ⟨qr, ⟨hdecomp, hcone⟩, hunique⟩ :=
    MonomialOrder.existsUnique_restricted_primitive_singleton_division
      (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) a ham ha hrad f hprim h
  have hactual : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (qr.2 : MvPowerSeries (Fin (n + 1)) V) = 0 := by
    intro i β hi
    apply hcone
    rw [hleading]
    exact (Finsupp.cons_zero_le_cons_iff β).mpr hi
  obtain ⟨P, ⟨hPdegree, hPimage⟩, _⟩ :=
    (restrictedFinFirst_actual_support_iff I n qr.2 d).mp hactual
  refine ⟨(qr.1, P), ⟨?_, hPdegree⟩, ?_⟩
  · rw [hPimage]
    exact hdecomp
  · rintro ⟨q', P'⟩ ⟨hdecomp', hPdegree'⟩
    have hcone' : ∀ index : Fin (n + 1) →₀ ℕ,
        MonomialOrder.restrictedLeadingExponent
          (MonomialOrder.lex : MonomialOrder (Fin (n + 1))) a ham f ≤ index →
          coeff index (polynomialRestrictedFinFirst I n P' :
            MvPowerSeries (Fin (n + 1)) V) = 0 := by
      intro index hindex
      let β := Finsupp.tail index
      let i := index 0
      have hindexeq : β.cons i = index := Finsupp.cons_tail index
      have hi : d ≤ i := (Finsupp.cons_zero_le_cons_iff β).mp (by
        rw [hleading, ← hindexeq] at hindex
        exact hindex)
      rw [← hindexeq, coeff_polynomialRestrictedFinFirst]
      have hz : P'.coeff i = 0 :=
        (Polynomial.degree_lt_iff_coeff_zero P' d).mp hPdegree' i hi
      simp only [hz, Subring.coe_zero, coeff_zero]
    have heq := hunique (q', polynomialRestrictedFinFirst I n P')
      ⟨hdecomp', hcone'⟩
    have hquotient : q' = qr.1 := congrArg
      (fun pair : adicallyRestrictedSubring (σ := Fin (n + 1)) I ×
        adicallyRestrictedSubring (σ := Fin (n + 1)) I => pair.1) heq
    have hremainder : polynomialRestrictedFinFirst I n P' = qr.2 := congrArg
      (fun pair : adicallyRestrictedSubring (σ := Fin (n + 1)) I ×
        adicallyRestrictedSubring (σ := Fin (n + 1)) I => pair.2) heq
    apply Prod.ext
    · exact hquotient
    · apply polynomialRestrictedFinFirst_injective I n
      exact hremainder.trans hPimage.symm

/-- Primitive scalar-top residues yield unique first-variable restricted
division for every dividend, including zero-degree divisors. -/
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

/-- Division of the distinguished monomial has a coefficientwise
remainder vanishing at every first exponent at least `d`. -/
theorem exists_firstVariable_monomial_division_of_scalar_top
    [IsAdicComplete (Ideal.span {a} : Ideal V) V]
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)
    (d : ℕ) (c : V ⧸ IsLocalRing.maximalIdeal V)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c) (hc : c ≠ 0) :
    ∃ q : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}),
      ∃ P : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a})),
        polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d) =
          q * f + polynomialRestrictedFinFirst (Ideal.span {a}) n P ∧
        P.degree < (d : WithBot ℕ) ∧
        ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
          coeff (β.cons i)
            (polynomialRestrictedFinFirst (Ideal.span {a}) n P :
              MvPowerSeries (Fin (n + 1)) V) = 0 := by
  obtain ⟨⟨q, P⟩, ⟨hdecomp, hPdegree⟩, _⟩ :=
    existsUnique_firstVariable_division_of_scalar_top n a ham ha hrad f hprim
      d c hdegree htop hc
      (polynomialRestrictedFinFirst (Ideal.span {a}) n (Polynomial.X ^ d))
  refine ⟨q, P, hdecomp, hPdegree, ?_⟩
  intro i β hi
  rw [coeff_polynomialRestrictedFinFirst]
  have hz : P.coeff i = 0 :=
    (Polynomial.degree_lt_iff_coeff_zero P d).mp hPdegree i hi
  simp only [hz, Subring.coe_zero, coeff_zero]

end MvPowerSeries
