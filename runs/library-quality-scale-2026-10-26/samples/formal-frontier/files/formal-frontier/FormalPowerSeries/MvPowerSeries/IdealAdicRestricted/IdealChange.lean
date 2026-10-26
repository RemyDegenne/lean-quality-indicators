/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted
public import Mathlib.RingTheory.Ideal.Operations

public section

/-!
# Change of defining ideal for restricted power series

Increasing the ideal preserves coefficientwise adic restriction. The resulting
inclusion of restricted subrings gives a polynomial reduction modulo any
larger ideal, with coefficients in `R ⧸ J`.

No finiteness, completeness, separatedness or nontriviality is assumed.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- Restriction for an ideal implies restriction for any larger ideal. -/
theorem IsAdicallyRestricted.mono {I J : Ideal R} {f : MvPowerSeries σ R}
    (hf : IsAdicallyRestricted I f) (hIJ : I ≤ J) : IsAdicallyRestricted J f := by
  intro k
  exact (hf k).subset (by
    intro d hd hI
    exact hd ((pow_le_pow_left' hIJ k) hI))

/-- The ideal-adically restricted subring is monotone in its defining ideal. -/
theorem adicallyRestrictedSubring_mono {I J : Ideal R} (hIJ : I ≤ J) :
    adicallyRestrictedSubring (σ := σ) I ≤ adicallyRestrictedSubring J := by
  intro f hf
  exact (mem_adicallyRestrictedSubring J f).mpr
    (((mem_adicallyRestrictedSubring I f).mp hf).mono hIJ)

/-- The identity on raw series, regarded as an inclusion into the subring
restricted for a larger ideal. -/
noncomputable def restrictAlongIdeal (I J : Ideal R) (hIJ : I ≤ J) :
    adicallyRestrictedSubring (σ := σ) I →+* adicallyRestrictedSubring (σ := σ) J :=
  Subring.inclusion (adicallyRestrictedSubring_mono hIJ)

@[simp]
theorem restrictAlongIdeal_coe (I J : Ideal R) (hIJ : I ≤ J)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    (restrictAlongIdeal I J hIJ f : MvPowerSeries σ R) = f := by
  simpa only [restrictAlongIdeal] using
    (Subring.coe_inclusion (adicallyRestrictedSubring_mono hIJ) f)

/-- Increasing the ideal does not identify distinct restricted series. -/
theorem restrictAlongIdeal_injective (I J : Ideal R) (hIJ : I ≤ J) :
    Function.Injective (restrictAlongIdeal (σ := σ) I J hIJ) :=
  Subring.inclusion_injective _

@[simp]
theorem restrictAlongIdeal_refl (I : Ideal R) :
    restrictAlongIdeal (σ := σ) I I le_rfl = RingHom.id _ := by
  apply RingHom.ext
  intro f
  apply Subtype.ext
  simp only [restrictAlongIdeal_coe, RingHom.id_apply]

/-- Ideal inclusions compose without changing the underlying series. -/
theorem restrictAlongIdeal_trans (I J K : Ideal R) (hIJ : I ≤ J) (hJK : J ≤ K) :
    (restrictAlongIdeal (σ := σ) J K hJK).comp (restrictAlongIdeal I J hIJ) =
      restrictAlongIdeal I K (hIJ.trans hJK) := by
  apply RingHom.ext
  intro f
  apply Subtype.ext
  simp only [RingHom.comp_apply, restrictAlongIdeal_coe]

@[simp]
theorem restrictAlongIdeal_polynomial (I J : Ideal R) (hIJ : I ≤ J)
    (p : MvPolynomial σ R) :
    restrictAlongIdeal I J hIJ (polynomialToRestricted I p) =
      polynomialToRestricted J p := by
  apply Subtype.ext
  simp only [restrictAlongIdeal_coe, polynomialToRestricted_coe]

/-- Finite polynomial reduction modulo a larger ideal, with coefficients
in `R ⧸ J` rather than `R ⧸ J ^ 1`. -/
noncomputable def reductionAtLargerIdeal (I J : Ideal R) (hIJ : I ≤ J) :
    adicallyRestrictedSubring (σ := σ) I →+* MvPolynomial σ (R ⧸ J) :=
  ((MvPolynomial.map (Ideal.Quotient.factor (le_of_eq (Submodule.pow_one J)))).comp
    (adicReduction J 1)).comp (restrictAlongIdeal I J hIJ)

/-- Coefficients of larger-ideal reduction are the coefficients of the
underlying series modulo that ideal. -/
@[simp]
theorem coeff_reductionAtLargerIdeal (I J : Ideal R) (hIJ : I ≤ J)
    (f : adicallyRestrictedSubring (σ := σ) I) (d : σ →₀ ℕ) :
    (reductionAtLargerIdeal I J hIJ f).coeff d =
      Ideal.Quotient.mk J (coeff d (f : MvPowerSeries σ R)) := by
  simp only [reductionAtLargerIdeal, RingHom.comp_apply, MvPolynomial.coeff_map,
    coeff_adicReduction, restrictAlongIdeal_coe, Ideal.Quotient.factor_mk]

@[simp]
theorem reductionAtLargerIdeal_polynomial (I J : Ideal R) (hIJ : I ≤ J)
    (p : MvPolynomial σ R) :
    reductionAtLargerIdeal I J hIJ (polynomialToRestricted I p) =
      MvPolynomial.map (Ideal.Quotient.mk J) p := by
  ext d
  simp only [coeff_reductionAtLargerIdeal, polynomialToRestricted_coe,
    MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

/-- Every quotient polynomial lifts through the restricted polynomial inclusion. -/
theorem reductionAtLargerIdeal_surjective (I J : Ideal R) (hIJ : I ≤ J) :
    Function.Surjective (reductionAtLargerIdeal (σ := σ) I J hIJ) := by
  intro p
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  exact ⟨polynomialToRestricted I q, reductionAtLargerIdeal_polynomial I J hIJ q⟩

/-- Vanishing of the finite reduction is exactly coefficientwise membership.
This makes no identification with an intrinsic ideal of the restricted ring. -/
theorem reductionAtLargerIdeal_eq_zero_iff (I J : Ideal R) (hIJ : I ≤ J)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    reductionAtLargerIdeal I J hIJ f = 0 ↔
      ∀ d, coeff d (f : MvPowerSeries σ R) ∈ J := by
  constructor
  · intro h d
    have hc := congrArg (fun p : MvPolynomial σ (R ⧸ J) => p.coeff d) h
    simpa only [coeff_reductionAtLargerIdeal, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, Ideal.Quotient.eq_zero_iff_mem] using hc
  · intro h
    ext d
    simpa only [coeff_reductionAtLargerIdeal, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, Ideal.Quotient.eq_zero_iff_mem] using h d

/-- Further reduction agrees with the quotient factor for a larger ideal. -/
theorem reductionAtLargerIdeal_map (I J K : Ideal R) (hIJ : I ≤ J) (hJK : J ≤ K)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    MvPolynomial.map (Ideal.Quotient.factor hJK) (reductionAtLargerIdeal I J hIJ f) =
      reductionAtLargerIdeal I K (hIJ.trans hJK) f := by
  ext d
  simp only [MvPolynomial.coeff_map, coeff_reductionAtLargerIdeal,
    Ideal.Quotient.factor_mk]

/-- Reducing after increasing the defining ideal gives the same polynomial. -/
theorem reductionAtLargerIdeal_restrictAlongIdeal (I J K : Ideal R)
    (hIJ : I ≤ J) (hJK : J ≤ K) (f : adicallyRestrictedSubring (σ := σ) I) :
    reductionAtLargerIdeal J K hJK (restrictAlongIdeal I J hIJ f) =
      reductionAtLargerIdeal I K (hIJ.trans hJK) f := by
  ext d
  simp only [coeff_reductionAtLargerIdeal, restrictAlongIdeal_coe]

end MvPowerSeries
