/- SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents -/
module

public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.Ideal.Quotient.Defs

public section

/-!
# Ideal-adically restricted multivariate power series

A series is restricted when, modulo every power of an ideal of its coefficient ring,
only finitely many coefficients remain nonzero. The finite reductions are actual
multivariate polynomials, with no finiteness assumption on the variables.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

@[expose] public section

/-- Coefficientwise ideal-adic decay, with finitely many exceptions at each level. -/
def IsAdicallyRestricted (I : Ideal R) (f : MvPowerSeries σ R) : Prop :=
  ∀ k : ℕ, {m : σ →₀ ℕ | coeff m f ∉ I ^ k}.Finite

end

/-- A quotient series is polynomial exactly when only finitely many coefficients
survive reduction modulo the chosen ideal power. -/
theorem finite_exception_iff_map_mem_poly_range (I : Ideal R) (k : ℕ)
    (f : MvPowerSeries σ R) :
    {m : σ →₀ ℕ | coeff m f ∉ I ^ k}.Finite ↔
      map (Ideal.Quotient.mk (I ^ k)) f ∈
        (MvPolynomial.coeToMvPowerSeries.ringHom
          (σ := σ) (R := R ⧸ I ^ k)).range := by
  classical
  constructor
  · intro h
    let s := h.toFinset
    refine ⟨truncFinset (R ⧸ I ^ k) s (map (Ideal.Quotient.mk (I ^ k)) f), ?_⟩
    apply MvPowerSeries.ext
    intro m
    by_cases hm : m ∈ s
    · simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coeff_coe, coeff_truncFinset_of_mem _ hm]
    · have hmem : coeff m f ∈ I ^ k := by
        by_contra hnot
        exact hm (h.mem_toFinset.mpr hnot)
      simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coeff_coe, coeff_truncFinset_eq_zero _ hm, coeff_map] using
        ((Ideal.Quotient.eq_zero_iff_mem).2 hmem).symm
  · rintro ⟨p, hp⟩
    have hs : {m : σ →₀ ℕ | coeff m f ∉ I ^ k} = (p.support : Set (σ →₀ ℕ)) := by
      ext m
      have hc : p.coeff m = Ideal.Quotient.mk (I ^ k) (coeff m f) := by
        have heq := congrArg (MvPowerSeries.coeff m) hp
        simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          MvPolynomial.coeff_coe, coeff_map] using heq
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, MvPolynomial.mem_support_iff,
        hc, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    rw [hs]
    exact p.support.finite_toSet

/-- Ideal-adic decay characterized at all levels by polynomial quotient images. -/
theorem isAdicallyRestricted_iff_map_mem_poly_range (I : Ideal R)
    (f : MvPowerSeries σ R) :
    IsAdicallyRestricted I f ↔
      ∀ k : ℕ, map (Ideal.Quotient.mk (I ^ k)) f ∈
        (MvPolynomial.coeToMvPowerSeries.ringHom
          (σ := σ) (R := R ⧸ I ^ k)).range := by
  simp only [IsAdicallyRestricted, finite_exception_iff_map_mem_poly_range]

/-- The subring of series with coefficientwise ideal-adic decay. -/
noncomputable def adicallyRestrictedSubring (I : Ideal R) : Subring (MvPowerSeries σ R) :=
  ⨅ k : ℕ, ((MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := σ) (R := R ⧸ I ^ k)).range).comap
      (map (Ideal.Quotient.mk (I ^ k)))

@[simp]
theorem mem_adicallyRestrictedSubring (I : Ideal R) (f : MvPowerSeries σ R) :
    f ∈ adicallyRestrictedSubring I ↔ IsAdicallyRestricted I f := by
  rw [isAdicallyRestricted_iff_map_mem_poly_range]
  simp only [adicallyRestrictedSubring, Subring.mem_iInf, Subring.mem_comap]

/-- Coefficientwise change of ring commutes with polynomial inclusion. -/
theorem map_polynomial_coe {S : Type*} [CommRing S] (g : R →+* S)
    (p : MvPolynomial σ R) :
    map g (p : MvPowerSeries σ R) =
      (MvPolynomial.map g p : MvPowerSeries σ S) := by
  ext m
  simp only [coeff_map, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

/-- Any polynomial is restricted for any ideal. -/
theorem isAdicallyRestricted_polynomial (I : Ideal R) (p : MvPolynomial σ R) :
    IsAdicallyRestricted I (p : MvPowerSeries σ R) := by
  apply (isAdicallyRestricted_iff_map_mem_poly_range I _).2
  intro k
  exact ⟨MvPolynomial.map (Ideal.Quotient.mk (I ^ k)) p,
    by simpa only [MvPolynomial.coeToMvPowerSeries.ringHom_apply] using
      (map_polynomial_coe (Ideal.Quotient.mk (I ^ k)) p).symm⟩

/-- The native polynomial inclusion, with codomain restricted to the decay subring. -/
noncomputable def polynomialToRestricted (I : Ideal R) :
    MvPolynomial σ R →+* adicallyRestrictedSubring (σ := σ) I :=
  (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := R)).codRestrict _
    (fun p => (mem_adicallyRestrictedSubring I _).2 (isAdicallyRestricted_polynomial I p))

@[simp]
theorem polynomialToRestricted_coe (I : Ideal R) (p : MvPolynomial σ R) :
    ((polynomialToRestricted (σ := σ) I p : adicallyRestrictedSubring (σ := σ) I) :
      MvPowerSeries σ R) = p := by
  simp only [polynomialToRestricted, RingHom.codRestrict_apply,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply]

private noncomputable def reductionPolynomial (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) : MvPolynomial σ (R ⧸ I ^ k) :=
  Classical.choose ((isAdicallyRestricted_iff_map_mem_poly_range I (f : MvPowerSeries σ R)).1
    ((mem_adicallyRestrictedSubring I (f : MvPowerSeries σ R)).1 f.property) k)

private theorem reductionPolynomial_spec (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    ((reductionPolynomial I k f : MvPolynomial σ (R ⧸ I ^ k)) :
      MvPowerSeries σ (R ⧸ I ^ k)) =
        map (Ideal.Quotient.mk (I ^ k)) (f : MvPowerSeries σ R) := by
  simpa only [reductionPolynomial, MvPolynomial.coeToMvPowerSeries.ringHom_apply] using
    Classical.choose_spec ((isAdicallyRestricted_iff_map_mem_poly_range I
      (f : MvPowerSeries σ R)).1
      ((mem_adicallyRestrictedSubring I (f : MvPowerSeries σ R)).1 f.property) k)

/-- Finite polynomial reduction of a restricted series modulo `I ^ k`. -/
noncomputable def adicReduction (I : Ideal R) (k : ℕ) :
    adicallyRestrictedSubring (σ := σ) I →+* MvPolynomial σ (R ⧸ I ^ k) where
  toFun := reductionPolynomial I k
  map_zero' := by
    apply MvPolynomial.coe_injective σ (R ⧸ I ^ k)
    simp only [reductionPolynomial_spec, Subring.coe_zero, map_zero, MvPolynomial.coe_zero]
  map_one' := by
    apply MvPolynomial.coe_injective σ (R ⧸ I ^ k)
    simp only [reductionPolynomial_spec, Subring.coe_one, map_one, MvPolynomial.coe_one]
  map_add' f g := by
    apply MvPolynomial.coe_injective σ (R ⧸ I ^ k)
    simp only [reductionPolynomial_spec, Subring.coe_add, map_add, MvPolynomial.coe_add]
  map_mul' f g := by
    apply MvPolynomial.coe_injective σ (R ⧸ I ^ k)
    simp only [reductionPolynomial_spec, Subring.coe_mul, map_mul, MvPolynomial.coe_mul]

/-- Polynomial inclusion of reduction agrees with quotienting all coefficients. -/
theorem adicReduction_coe (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    ((adicReduction I k f : MvPolynomial σ (R ⧸ I ^ k)) :
      MvPowerSeries σ (R ⧸ I ^ k)) =
        map (Ideal.Quotient.mk (I ^ k)) (f : MvPowerSeries σ R) :=
  reductionPolynomial_spec I k f

/-- Each coefficient of finite reduction is the original coefficient modulo `I ^ k`. -/
@[simp]
theorem coeff_adicReduction (I : Ideal R) (k : ℕ)
    (f : adicallyRestrictedSubring (σ := σ) I) (m : σ →₀ ℕ) :
    (adicReduction I k f).coeff m =
      Ideal.Quotient.mk (I ^ k) (coeff m (f : MvPowerSeries σ R)) := by
  have hc := congrArg (MvPowerSeries.coeff m) (adicReduction_coe I k f)
  simpa only [MvPolynomial.coeff_coe, coeff_map] using hc

/-- Reducing a polynomial through the restricted subring is native coefficientwise
polynomial reduction. -/
@[simp]
theorem adicReduction_polynomial (I : Ideal R) (k : ℕ) (p : MvPolynomial σ R) :
    adicReduction I k (polynomialToRestricted I p) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ k)) p := by
  apply MvPolynomial.coe_injective σ (R ⧸ I ^ k)
  rw [adicReduction_coe, polynomialToRestricted_coe, map_polynomial_coe]

/-- Every quotient polynomial has a restricted-series lift. -/
theorem adicReduction_surjective (I : Ideal R) (k : ℕ) :
    Function.Surjective (adicReduction (σ := σ) I k) := by
  intro p
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective
    (Ideal.Quotient.mk (I ^ k)) (Ideal.Quotient.mk_surjective) p
  exact ⟨polynomialToRestricted I q, adicReduction_polynomial I k q⟩

end MvPowerSeries
