/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationResidue
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.UnitDetection
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

public section

/-!
# Unit reflection from polynomial residue

The polynomial residue detects units of principal-adically restricted series
when the principal ideal has radical equal to the local maximal ideal and the
coefficient ring is adically complete.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {R σ : Type*} [CommRing R]

section UnitReflection

variable [IsLocalRing R] (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a}) R]

include hrad
/-- A unit of the genuine residue polynomial lifts to a unit of the restricted
series under the stated radical and completeness hypotheses. This proof uses
completeness through the published coefficient/radical unit criterion. -/
theorem isUnit_of_isUnit_restrictedResidueHom
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hf : IsUnit (restrictedResidueHom a ham f)) : IsUnit f := by
  classical
  obtain ⟨c, hc, hres⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hf
  apply (isUnit_adicallyRestricted_iff_coeff_radical (Ideal.span {a}) f).2
  constructor
  · apply IsLocalRing.notMem_maximalIdeal.mp
    have hcoeff : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
        (coeff 0 (f : MvPowerSeries σ R)) = c := by
      simpa [coeff_restrictedResidueHom] using
        congrArg (fun p : MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R) =>
          p.coeff 0) hres
    intro hmem
    exact hc.ne_zero (hcoeff.symm.trans ((Ideal.Quotient.eq_zero_iff_mem).mpr hmem))
  · intro α hα
    rw [hrad]
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    have hcoeff := congrArg (fun p : MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R) =>
      p.coeff α) hres
    simpa [coeff_restrictedResidueHom, hα, Ne.symm hα] using hcoeff

end UnitReflection

section ValuationUnitReflection

variable [IsDomain R] [ValuationRing R] (a : R)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    [IsAdicComplete (Ideal.span {a}) R]

include hrad
/-- The genuine valuation-domain residue detects restricted-series units. -/
theorem isUnit_of_isUnit_restrictedResidue
    (f : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hf : IsUnit (restrictedResidue a ham f)) : IsUnit f :=
  isUnit_of_isUnit_restrictedResidueHom a ham hrad f
    (by simpa only [restrictedResidueHom_apply] using hf)

end ValuationUnitReflection

end MvPowerSeries
