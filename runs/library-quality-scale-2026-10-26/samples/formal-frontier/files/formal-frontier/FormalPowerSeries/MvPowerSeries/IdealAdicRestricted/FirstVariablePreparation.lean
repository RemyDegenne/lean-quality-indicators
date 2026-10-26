/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableDivision
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.FirstVariableUnit

public section

/-!
# Preparation in the first variable of a restricted power series

Dividing the distinguished monomial by a primitive series with nonzero scalar
top residue produces a monic polynomial in the first variable. The quotient is
a unit, and division uniqueness makes the entire prepared pair unique, even
against competitors whose quotient is not assumed to be a unit.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]
    (n : ℕ) (a : V) (ham : a ∈ IsLocalRing.maximalIdeal V)
    [IsAdicComplete (Ideal.span {a}) V]

/-- A primitive restricted series whose first-variable residue has a nonzero
scalar top coefficient has a unique monic polynomial preparation. Uniqueness
does not require the competing quotient to be a unit. -/
theorem existsUnique_firstVariable_preparation_of_scalar_top_of_primitive
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ =>
      coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)
    (d : ℕ) (c : IsLocalRing.ResidueField V)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c) (hc : c ≠ 0) :
    ∃ (u : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
      (G : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
      IsUnit u ∧ G.Monic ∧ G.degree = (d : WithBot ℕ) ∧
        polynomialRestrictedFinFirst (Ideal.span {a}) n G = u * f ∧
        ∀ (v : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
          (H : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
          H.Monic → H.degree = (d : WithBot ℕ) →
          polynomialRestrictedFinFirst (Ideal.span {a}) n H = v * f →
          v = u ∧ H = G := by
  classical
  let I : Ideal V := Ideal.span {a}
  obtain ⟨⟨u, R⟩, ⟨hdivision, hRdegree⟩, hunique⟩ :=
    existsUnique_firstVariable_division_of_scalar_top n a ham ha hrad f hprim
      d c hdegree htop hc (polynomialRestrictedFinFirst I n (Polynomial.X ^ d))
  have hsupport : ∀ (i : ℕ) (β : Fin n →₀ ℕ), d ≤ i →
      coeff (β.cons i) (polynomialRestrictedFinFirst I n R :
        MvPowerSeries (Fin (n + 1)) V) = 0 := by
    intro i β hi
    rw [coeff_polynomialRestrictedFinFirst]
    have hzero : R.coeff i = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero R d).mp hRdegree i hi
    simp only [hzero, Subring.coe_zero, coeff_zero]
  have hu : IsUnit u :=
    isUnit_quotient_of_restrictedFinFirst_division a ham hrad n d f u
      (polynomialRestrictedFinFirst I n R) c hc hdegree htop hdivision hsupport
  let G : Polynomial (adicallyRestrictedSubring (σ := Fin n) I) := Polynomial.X ^ d - R
  have hGmonic : G.Monic := Polynomial.monic_X_pow_sub hRdegree
  have hGdegree : G.degree = (d : WithBot ℕ) := by
    change (Polynomial.X ^ d - R).degree = (d : WithBot ℕ)
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by simpa only [Polynomial.degree_X_pow]
      using hRdegree), Polynomial.degree_X_pow]
  have hGeq : polynomialRestrictedFinFirst I n G = u * f := by
    change polynomialRestrictedFinFirst I n (Polynomial.X ^ d - R) = u * f
    rw [map_sub, hdivision]
    ring
  refine ⟨u, G, hu, hGmonic, hGdegree, hGeq, ?_⟩
  intro v H hHmonic hHdegree hHeq
  have hHdifference : (Polynomial.X ^ d - H).degree < (d : WithBot ℕ) := by
    have hsame : (Polynomial.X ^ d : Polynomial (adicallyRestrictedSubring
        (σ := Fin n) I)).degree = H.degree := by
      rw [Polynomial.degree_X_pow, hHdegree]
    have hleading : (Polynomial.X ^ d : Polynomial (adicallyRestrictedSubring
        (σ := Fin n) I)).leadingCoeff = H.leadingCoeff := by
      rw [(Polynomial.monic_X_pow d).leadingCoeff, hHmonic.leadingCoeff]
    simpa only [Polynomial.degree_X_pow] using
      (Polynomial.degree_sub_lt_left hsame (Polynomial.monic_X_pow d).ne_zero hleading)
  have hHdivision : polynomialRestrictedFinFirst I n (Polynomial.X ^ d) =
      v * f + polynomialRestrictedFinFirst I n (Polynomial.X ^ d - H) := by
    rw [map_sub, hHeq]
    ring
  have hpair := hunique (v, Polynomial.X ^ d - H) ⟨hHdivision, hHdifference⟩
  constructor
  · exact congrArg Prod.fst hpair
  · have hR : Polynomial.X ^ d - H = R := congrArg Prod.snd hpair
    change H = Polynomial.X ^ d - R
    rw [← hR]
    ring

/-- A nonzero scalar top residue coefficient already implies actual-coefficient
primitivity, so no separate primitivity hypothesis is needed for preparation. -/
theorem existsUnique_firstVariable_preparation_of_scalar_top
    (ha : a ≠ 0)
    (hrad : (Ideal.span {a} : Ideal V).radical = IsLocalRing.maximalIdeal V)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
    (d : ℕ) (c : IsLocalRing.ResidueField V)
    (hdegree : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).natDegree = d)
    (htop : (MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)).coeff d =
      MvPolynomial.C c) (hc : c ≠ 0) :
    ∃ (u : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
      (G : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
      IsUnit u ∧ G.Monic ∧ G.degree = (d : WithBot ℕ) ∧
        polynomialRestrictedFinFirst (Ideal.span {a}) n G = u * f ∧
        ∀ (v : adicallyRestrictedSubring (σ := Fin (n + 1)) (Ideal.span {a}))
          (H : Polynomial (adicallyRestrictedSubring (σ := Fin n) (Ideal.span {a}))),
          H.Monic → H.degree = (d : WithBot ℕ) →
          polynomialRestrictedFinFirst (Ideal.span {a}) n H = v * f →
          v = u ∧ H = G := by
  let index : Fin (n + 1) →₀ ℕ := (0 : Fin n →₀ ℕ).cons d
  have hresidue : (restrictedResidue a ham f).coeff index = c := by
    have hcoeff := MvPolynomial.finSuccEquiv_coeff_coeff
      (0 : Fin n →₀ ℕ) (restrictedResidue a ham f) d
    have hscalar := congrArg
      (fun p : MvPolynomial (Fin n) (IsLocalRing.ResidueField V) => p.coeff 0) htop
    exact hcoeff.symm.trans (hscalar.trans (MvPolynomial.coeff_zero_C c))
  have hnot : coeff index (f : MvPowerSeries (Fin (n + 1)) V) ∉
      IsLocalRing.maximalIdeal V := by
    intro hmem
    apply hc
    rw [← hresidue, coeff_restrictedResidue]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hunit : IsUnit (coeff index (f : MvPowerSeries (Fin (n + 1)) V)) :=
    not_not.mp (by simpa only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hnot)
  have hprim : Ideal.span (Set.range (fun exponent : Fin (n + 1) →₀ ℕ =>
      coeff exponent (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤ :=
    (Ideal.span (Set.range (fun exponent : Fin (n + 1) →₀ ℕ =>
      coeff exponent (f : MvPowerSeries (Fin (n + 1)) V)))).eq_top_of_isUnit_mem
        (Ideal.subset_span (Set.mem_range_self index)) hunit
  exact existsUnique_firstVariable_preparation_of_scalar_top_of_primitive n a ham
    ha hrad f hprim d c hdegree htop hc

end MvPowerSeries
