/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearExtension
public import MultivariatePolynomials.LinearDivision

@[expose] public section

/-!
# Fixed polynomial division on ideal-adically restricted series

The polynomial quotient coordinates and remainder extend linearly to restricted
series. The quotient is a function family for arbitrary indices; a finite family
of divisors yields a decomposition inside the restricted subring.
-/

set_option warningAsError true

namespace MonomialOrder

variable {σ ι R : Type*} [CommRing R]
variable (I : Ideal R) [IsAdicComplete I R]
variable (m : MonomialOrder σ) (b : ι → MvPolynomial σ R)
variable (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))

/-- The fixed `R`-linear restricted-series remainder of polynomial division. -/
noncomputable def restrictedDivisionRemainder :
    MvPowerSeries.adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      MvPowerSeries.adicallyRestrictedSubring (σ := σ) I :=
  MvPowerSeries.restrictedLinearExtension I (m.linearDivisionRemainder b hb)

/-- Coordinatewise polynomial division extends to a function-valued, `R`-linear
quotient. For arbitrary `ι` this is not a finitely supported family. -/
noncomputable def restrictedDivisionQuotient :
    MvPowerSeries.adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      (ι → MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :=
  LinearMap.pi fun i =>
    MvPowerSeries.restrictedLinearExtension I
      ((Finsupp.lapply i).comp (m.linearDivisionQuotient b hb))

@[simp]
theorem restrictedDivisionQuotient_apply
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) (i : ι) :
    restrictedDivisionQuotient I m b hb f i =
      MvPowerSeries.restrictedLinearExtension I
        ((Finsupp.lapply i).comp (m.linearDivisionQuotient b hb)) f :=
  rfl

/-- The restricted remainder agrees with fixed polynomial division on polynomials. -/
theorem restrictedDivisionRemainder_polynomial (p : MvPolynomial σ R) :
    restrictedDivisionRemainder I m b hb (MvPowerSeries.polynomialToRestricted I p) =
      MvPowerSeries.polynomialToRestricted I (m.linearDivisionRemainder b hb p) :=
  MvPowerSeries.restrictedLinearExtension_polynomial I _ p

/-- Each quotient coordinate agrees with fixed polynomial division on polynomials. -/
theorem restrictedDivisionQuotient_polynomial (p : MvPolynomial σ R) (i : ι) :
    restrictedDivisionQuotient I m b hb (MvPowerSeries.polynomialToRestricted I p) i =
      MvPowerSeries.polynomialToRestricted I (m.linearDivisionQuotient b hb p i) := by
  rw [restrictedDivisionQuotient_apply,
    MvPowerSeries.restrictedLinearExtension_polynomial]
  rfl

/-- The remainder preserves the kernel of every coefficientwise reduction. -/
theorem restrictedDivisionRemainder_preserves_ker (n : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (hf : MvPowerSeries.adicReduction I n f = 0) :
    MvPowerSeries.adicReduction I n (restrictedDivisionRemainder I m b hb f) = 0 :=
  MvPowerSeries.restrictedLinearExtension_preserves_ker I _ n f hf

/-- Each quotient coordinate preserves every coefficientwise reduction kernel. -/
theorem restrictedDivisionQuotient_preserves_ker (n : ℕ)
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I)
    (hf : MvPowerSeries.adicReduction I n f = 0) (i : ι) :
    MvPowerSeries.adicReduction I n (restrictedDivisionQuotient I m b hb f i) = 0 := by
  rw [restrictedDivisionQuotient_apply]
  exact MvPowerSeries.restrictedLinearExtension_preserves_ker I _ n f hf

private theorem restricted_eq_of_reductions
    {f g : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I}
    (h : ∀ n, MvPowerSeries.adicReduction I n f = MvPowerSeries.adicReduction I n g) :
    f = g := by
  apply (MvPowerSeries.adicallyRestrictedEquivAdicCompletion (σ := σ) I).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (MvPowerSeries.adicPolynomialLevelEquiv (σ := σ) I n).injective
  simpa only [MvPowerSeries.adicallyRestrictedEquivAdicCompletion_eval] using h n

/-- Fixed division by finitely many polynomial divisors reconstructs the restricted
series in the existing restricted subring. -/
theorem restrictedDivision_decomposition [Fintype ι]
    (f : MvPowerSeries.adicallyRestrictedSubring (σ := σ) I) :
    f = (∑ i, restrictedDivisionQuotient I m b hb f i *
      MvPowerSeries.polynomialToRestricted I (b i)) +
      restrictedDivisionRemainder I m b hb f := by
  classical
  apply restricted_eq_of_reductions I
  intro n
  obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective
    (MvPowerSeries.adicReduction I n f)
  have hlevel : MvPowerSeries.adicReduction I n
      (MvPowerSeries.polynomialToRestricted I p) = MvPowerSeries.adicReduction I n f := by
    simpa only [MvPowerSeries.adicReduction_polynomial] using hp
  have hrem : MvPowerSeries.adicReduction I n (restrictedDivisionRemainder I m b hb f) =
      MvPowerSeries.adicReduction I n
        (MvPowerSeries.polynomialToRestricted I (m.linearDivisionRemainder b hb p)) := by
    rw [restrictedDivisionRemainder,
      MvPowerSeries.adicReduction_restrictedLinearExtension,
      MvPowerSeries.adicReduction_polynomial,
      ← MvPowerSeries.polynomialLinearMapMod_map, hp]
  have hquot (i : ι) :
      MvPowerSeries.adicReduction I n (restrictedDivisionQuotient I m b hb f i) =
        MvPowerSeries.adicReduction I n
          (MvPowerSeries.polynomialToRestricted I (m.linearDivisionQuotient b hb p i)) := by
    rw [restrictedDivisionQuotient_apply,
      MvPowerSeries.adicReduction_restrictedLinearExtension,
      MvPowerSeries.adicReduction_polynomial]
    calc
      MvPowerSeries.polynomialLinearMapMod I n
          ((Finsupp.lapply i).comp (m.linearDivisionQuotient b hb))
          (MvPowerSeries.adicReduction I n f) =
        MvPowerSeries.polynomialLinearMapMod I n
          ((Finsupp.lapply i).comp (m.linearDivisionQuotient b hb))
          (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p) := by rw [hp]
      _ = MvPolynomial.map (Ideal.Quotient.mk (I ^ n))
          (((Finsupp.lapply i).comp (m.linearDivisionQuotient b hb)) p) :=
        MvPowerSeries.polynomialLinearMapMod_map I n _ p
      _ = _ := by simp only [LinearMap.comp_apply, Finsupp.lapply_apply]
  rw [← hlevel]
  have hpoly : p =
      (∑ i, (m.linearDivisionQuotient b hb p i) * b i) +
        m.linearDivisionRemainder b hb p := by
    calc
      p = Finsupp.linearCombination (MvPolynomial σ R) b
            (m.linearDivisionQuotient b hb p) + m.linearDivisionRemainder b hb p :=
        m.linearDivision_decomposition b hb p
      _ = _ := by
        rw [Finsupp.linearCombination_apply,
          (m.linearDivisionQuotient b hb p).sum_fintype
            (fun i q => q • b i) (by simp)]
        simp only [smul_eq_mul]
  rw [hpoly]
  simp only [map_add, map_sum, map_mul, map_sum, hrem, ← hquot]

/-- A coefficient in the componentwise leading cone of any divisor actually
vanishes in the restricted remainder, not just in each finite reduction. -/
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
