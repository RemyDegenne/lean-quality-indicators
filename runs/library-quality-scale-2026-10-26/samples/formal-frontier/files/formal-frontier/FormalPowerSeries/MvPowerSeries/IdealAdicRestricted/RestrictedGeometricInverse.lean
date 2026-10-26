/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.InverseLimit
public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.LinearQuotient

public section

/-!
# Geometric inverses on ideal-adically restricted series

A linear endomorphism that raises the coefficientwise reduction kernels has a
two-sided geometric inverse. No identification with the intrinsic adic filtration
on the restricted-series ring is needed.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

private noncomputable def restrictedGeometricPartial (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I)) (n : ℕ) :
    Module.End R (adicallyRestrictedSubring (σ := σ) I) :=
  ∑ j ∈ Finset.range n, E ^ j

private theorem restrictedReduction_zero (I : Ideal R)
    (x : adicallyRestrictedSubring (σ := σ) I) : adicReduction I 0 x = 0 := by
  have h : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  apply MvPolynomial.ext
  intro index
  exact @Subsingleton.elim _ h _ _

private theorem restrictedReduction_mono (I : Ideal R) {n m : ℕ} (hnm : n ≤ m)
    (x : adicallyRestrictedSubring (σ := σ) I)
    (hx : adicReduction I m x = 0) : adicReduction I n x = 0 := by
  rw [← adicReduction_factorPow I hnm x, hx, map_zero]

private theorem restrictedGeometric_power_kernel (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n ((E ^ n) x) = 0 := by
  induction n with
  | zero => simpa using restrictedReduction_zero I x
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply] using hE n _ ih

private theorem restrictedGeometric_preserves_kernel (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I)
    (hx : adicReduction I n x = 0) : adicReduction I n (E x) = 0 :=
  restrictedReduction_mono I (Nat.le_succ n) _ (hE n x hx)

private theorem restrictedGeometric_power_preserves_kernel (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (n j : ℕ) (x : adicallyRestrictedSubring (σ := σ) I)
    (hx : adicReduction I n x = 0) : adicReduction I n ((E ^ j) x) = 0 := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    simpa only [pow_succ', Module.End.mul_apply] using
      restrictedGeometric_preserves_kernel I E hE n _ ih

private theorem restrictedGeometricPartial_reduction (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    {n m : ℕ} (hnm : n ≤ m) (x : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedGeometricPartial I E m x) =
      adicReduction I n (restrictedGeometricPartial I E n x) := by
  simp only [restrictedGeometricPartial, LinearMap.sum_apply, map_sum]
  symm
  apply Finset.sum_subset (Finset.range_mono hnm)
  intro j hj hjnot
  apply restrictedReduction_mono I (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hjnot))
  exact restrictedGeometric_power_kernel I E hE j x

private theorem restrictedGeometric_levels_compat (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (x : adicallyRestrictedSubring (σ := σ) I)
    {n m : ℕ} (hnm : n ≤ m) :
    MvPolynomial.map (Ideal.Quotient.factorPow I hnm)
        (adicReduction I m (restrictedGeometricPartial I E m x)) =
      adicReduction I n (restrictedGeometricPartial I E n x) := by
  rw [adicReduction_factorPow, restrictedGeometricPartial_reduction I E hE hnm]

private theorem restrictedGeometric_nativeTransition (J : Ideal (MvPolynomial σ R))
    {n m : ℕ} (hnm : n ≤ m) (x : MvPolynomial σ R ⧸ J ^ m) :
    AdicCompletion.transitionMap J (MvPolynomial σ R) hnm
        ((Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
          (Ideal.mul_top (J ^ m))).symm x) =
      (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top (J ^ n))).symm (Ideal.Quotient.factorPow J hnm x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk]
  rfl

private noncomputable def restrictedGeometricCompletion (I : Ideal R)
    (polynomials : ∀ n, MvPolynomial σ (R ⧸ I ^ n))
    (hpolynomials : ∀ {n m : ℕ} (hnm : n ≤ m),
      MvPolynomial.map (Ideal.Quotient.factorPow I hnm) (polynomials m) =
        polynomials n) :
    AdicCompletion (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
      (MvPolynomial σ R) :=
  ⟨fun n =>
      (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n))).symm
        ((adicPolynomialLevelEquiv (σ := σ) I n).symm (polynomials n)), by
    intro n m hnm
    rw [restrictedGeometric_nativeTransition]
    change (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
      (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n))).symm
        (Ideal.Quotient.factorPow _ hnm
          ((adicPolynomialLevelEquiv (σ := σ) I m).symm (polynomials m))) =
      (Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n))).symm
          ((adicPolynomialLevelEquiv (σ := σ) I n).symm (polynomials n))
    congr 1
    apply (adicPolynomialLevelEquiv (σ := σ) I n).injective
    rw [adicPolynomialLevelEquiv_factorPow]
    simp only [RingEquiv.apply_symm_apply, hpolynomials hnm]⟩

private theorem restrictedGeometricCompletion_eval (I : Ideal R)
    (polynomials : ∀ n, MvPolynomial σ (R ⧸ I ^ n))
    (hpolynomials : ∀ {n m : ℕ} (hnm : n ≤ m),
      MvPolynomial.map (Ideal.Quotient.factorPow I hnm) (polynomials m) =
        polynomials n) (n : ℕ) :
    adicPolynomialLevelEquiv (σ := σ) I n
        (AdicCompletion.evalₐ _ n
          (restrictedGeometricCompletion I polynomials hpolynomials)) = polynomials n := by
  change adicPolynomialLevelEquiv (σ := σ) I n
    ((Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
      (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n)))
      ((Ideal.quotientEquivAlgOfEq (MvPolynomial σ R)
        (Ideal.mul_top ((I.map (MvPolynomial.C : R →+* MvPolynomial σ R)) ^ n))).symm
        ((adicPolynomialLevelEquiv (σ := σ) I n).symm (polynomials n)))) = _
  rw [AlgEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem restrictedGeometric_separate (I : Ideal R) [IsAdicComplete I R]
    {x y : adicallyRestrictedSubring (σ := σ) I}
    (h : ∀ n, adicReduction I n x = adicReduction I n y) : x = y := by
  apply (adicallyRestrictedEquivAdicCompletion (σ := σ) I).injective
  apply AdicCompletion.ext_evalₐ
  intro n
  apply (adicPolynomialLevelEquiv (σ := σ) I n).injective
  simpa only [adicallyRestrictedEquivAdicCompletion_eval] using h n

private noncomputable def restrictedGeometricFun (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (x : adicallyRestrictedSubring (σ := σ) I) :
    adicallyRestrictedSubring (σ := σ) I :=
  (adicallyRestrictedEquivAdicCompletion I).symm
    (restrictedGeometricCompletion I
      (fun n => adicReduction I n (restrictedGeometricPartial I E n x))
      (restrictedGeometric_levels_compat I E hE x))

private theorem restrictedGeometricFun_reduction (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedGeometricFun I E hE x) =
      adicReduction I n (restrictedGeometricPartial I E n x) := by
  rw [restrictedGeometricFun, adicallyRestrictedEquivAdicCompletion_symm_eval,
    restrictedGeometricCompletion_eval]

/-- The geometric inverse to `id - E` for a coefficientwise filtration-raising
endomorphism of the existing restricted-series `R`-module. -/
noncomputable def restrictedGeometricInverse (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0) :
    Module.End R (adicallyRestrictedSubring (σ := σ) I) where
  toFun := restrictedGeometricFun I E hE
  map_add' x y := by
    apply restrictedGeometric_separate I
    intro n
    simp only [restrictedGeometricFun_reduction, map_add]
  map_smul' r x := by
    apply restrictedGeometric_separate I
    intro n
    change adicReduction I n (restrictedGeometricFun I E hE (r • x)) =
      adicReduction I n (r • restrictedGeometricFun I E hE x)
    calc
      adicReduction I n (restrictedGeometricFun I E hE (r • x)) =
          adicReduction I n (restrictedGeometricPartial I E n (r • x)) :=
        restrictedGeometricFun_reduction I E hE n (r • x)
      _ = adicReduction I n (r • restrictedGeometricPartial I E n x) := by
        rw [(restrictedGeometricPartial I E n).map_smul]
      _ = adicReduction I n (r • restrictedGeometricFun I E hE x) := by
        rw [← linearAdicReduction_apply I n (r • restrictedGeometricPartial I E n x),
          ← linearAdicReduction_apply I n (r • restrictedGeometricFun I E hE x)]
        rw [(linearAdicReduction I n).map_smul, (linearAdicReduction I n).map_smul]
        simp only [linearAdicReduction_apply, restrictedGeometricFun_reduction]

/-- At level `n`, the inverse is the finite geometric sum. -/
@[simp]
theorem restrictedGeometricInverse_reduction (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I) :
    adicReduction I n (restrictedGeometricInverse I E hE x) =
      adicReduction I n ((∑ j ∈ Finset.range n, E ^ j) x) :=
  restrictedGeometricFun_reduction I E hE n x

/-- The geometric inverse preserves every coefficientwise reduction kernel. -/
theorem restrictedGeometricInverse_preserves_ker (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I)
    (hx : adicReduction I n x = 0) :
    adicReduction I n (restrictedGeometricInverse I E hE x) = 0 := by
  rw [restrictedGeometricInverse_reduction]
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact restrictedGeometric_power_preserves_kernel I E hE n j x hx

private theorem restrictedGeometric_telescope_left (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I) :
    restrictedGeometricPartial I E n x - E (restrictedGeometricPartial I E n x) =
      x - (E ^ n) x := by
  have h := congrArg
    (fun f : Module.End R (adicallyRestrictedSubring (σ := σ) I) => f x)
    (mul_neg_geom_sum E n)
  simpa only [restrictedGeometricPartial, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] using h

private theorem restrictedGeometric_telescope_right (I : Ideal R)
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (n : ℕ) (x : adicallyRestrictedSubring (σ := σ) I) :
    restrictedGeometricPartial I E n (x - E x) = x - (E ^ n) x := by
  have h := congrArg
    (fun f : Module.End R (adicallyRestrictedSubring (σ := σ) I) => f x)
    (geom_sum_mul_neg E n)
  simpa only [restrictedGeometricPartial, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] using h

/-- The inverse is a right inverse of `id - E` (the operator applied after the sum). -/
theorem restrictedGeometricInverse_left_inv (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0) :
    (LinearMap.id - E).comp (restrictedGeometricInverse I E hE) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply restrictedGeometric_separate I
  intro n
  change adicReduction I n
    (restrictedGeometricInverse I E hE x - E (restrictedGeometricInverse I E hE x)) =
      adicReduction I n x
  have hdelta : adicReduction I n
      (restrictedGeometricInverse I E hE x - restrictedGeometricPartial I E n x) = 0 := by
    rw [map_sub, restrictedGeometricInverse_reduction]
    change adicReduction I n (restrictedGeometricPartial I E n x) -
      adicReduction I n (restrictedGeometricPartial I E n x) = 0
    exact sub_self _
  have hEdelta := restrictedGeometric_preserves_kernel I E hE n _ hdelta
  have heq : adicReduction I n (E (restrictedGeometricInverse I E hE x)) =
      adicReduction I n (E (restrictedGeometricPartial I E n x)) := by
    have hmap := congrArg (adicReduction I n)
      (E.map_sub (restrictedGeometricInverse I E hE x)
        (restrictedGeometricPartial I E n x))
    rw [hEdelta, map_sub] at hmap
    exact sub_eq_zero.mp hmap.symm
  rw [map_sub, restrictedGeometricInverse_reduction, heq]
  change adicReduction I n (restrictedGeometricPartial I E n x) -
    adicReduction I n (E (restrictedGeometricPartial I E n x)) = adicReduction I n x
  rw [← map_sub, restrictedGeometric_telescope_left,
    map_sub, restrictedGeometric_power_kernel I E hE n x, sub_zero]

/-- The inverse is a left inverse of `id - E` (the sum applied afterward). -/
theorem restrictedGeometricInverse_right_inv (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0) :
    (restrictedGeometricInverse I E hE).comp (LinearMap.id - E) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply restrictedGeometric_separate I
  intro n
  change adicReduction I n (restrictedGeometricInverse I E hE (x - E x)) =
    adicReduction I n x
  rw [restrictedGeometricInverse_reduction, ← restrictedGeometricPartial,
    restrictedGeometric_telescope_right, map_sub,
    restrictedGeometric_power_kernel I E hE n x, sub_zero]

/-- A right inverse of `id - E` is necessarily the geometric inverse; no
filtration-preservation assumption is imposed on the competing linear map. -/
theorem restrictedGeometricInverse_unique (I : Ideal R) [IsAdicComplete I R]
    (E : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hE : ∀ n x, adicReduction I n x = 0 → adicReduction I (n + 1) (E x) = 0)
    (U : Module.End R (adicallyRestrictedSubring (σ := σ) I))
    (hU : (LinearMap.id - E).comp U = LinearMap.id) :
    U = restrictedGeometricInverse I E hE := by
  apply LinearMap.ext
  intro x
  have hright := congrArg
    (fun f : Module.End R (adicallyRestrictedSubring (σ := σ) I) => f (U x))
    (restrictedGeometricInverse_right_inv I E hE)
  have hright' : restrictedGeometricInverse I E hE (U x - E (U x)) =
      U x := by
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using hright
  have hU' := congrArg
    (fun f : Module.End R (adicallyRestrictedSubring (σ := σ) I) => f x) hU
  have hU'' : U x - E (U x) = x := by
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using hU'
  calc
    U x = restrictedGeometricInverse I E hE (U x - E (U x)) :=
      hright'.symm
    _ = restrictedGeometricInverse I E hE x := by rw [hU'']

end MvPowerSeries
