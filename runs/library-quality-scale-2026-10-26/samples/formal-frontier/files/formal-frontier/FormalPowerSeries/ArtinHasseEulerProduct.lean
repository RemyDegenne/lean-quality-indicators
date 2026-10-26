/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.ArtinHasse
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.PowerSeries.Binomial

import FormalPowerSeries.Binomial
import FormalPowerSeries.UnitLogDerivative
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.PowerSeries.Order

/-!
# The Artin–Hasse Euler product

The Euler product for the rational Artin–Hasse exponential can be expressed
without introducing an infinite-product operation: its coefficient in degree
`k` agrees with every finite prefix whose cutoff is at least `k`. The factors
are the existing formal binomial series for `(1 - X^n)^(-μ(n)/n)`, indexed by
positive integers coprime to the prime `p`. No coefficient integrality or
analytic convergence hypothesis is involved.

## Scope

The identity is coefficientwise for finite products. No topological
infinite-product operation or analytic convergence assertion is introduced.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second
  edition (2002), Chapter I, (9.1), pp. 29–30.
* Mathlib's binomial-series, rescaling and substitution APIs.
-/

@[expose] public section

namespace ArithmeticFunction

open Classical in
private theorem sum_moebius_divisors_coprime (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d p), moebius d =
      if ∃ j : ℕ, p ^ j = n then (1 : ℤ) else 0 := by
  by_cases hn : n = 0
  · subst n
    have hpow : ¬ ∃ j : ℕ, p ^ j = 0 := by
      rintro ⟨j, hj⟩
      exact pow_ne_zero j hp.ne_zero hj
    simp only [Nat.divisors_zero, Finset.filter_empty, Finset.sum_empty, ite_eq_right hpow]
  have hdiv : n.divisors.filter (fun d => Nat.Coprime d p) = (ordCompl[p] n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hdp⟩
      exact ⟨Nat.dvd_ordCompl_of_dvd_not_dvd hdn (hp.coprime_iff_not_dvd.mp hdp.symm),
        (Nat.ordCompl_pos p hn).ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.ordCompl_dvd n p), hn⟩,
        ((Nat.coprime_ordCompl hp hn).of_dvd_right hd).symm⟩
  have hpow : ordCompl[p] n = 1 ↔ ∃ j : ℕ, p ^ j = n := by
    constructor
    · intro h
      exact ⟨n.factorization p, by simpa [h] using Nat.ordProj_mul_ordCompl_eq_self n p⟩
    · rintro ⟨j, rfl⟩
      exact Nat.ordCompl_self_pow hp
  rw [hdiv, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  simp only [hpow]

end ArithmeticFunction

namespace PowerSeries

private noncomputable abbrev eulerFactor (n : ℕ) : PowerSeries ℚ :=
  subst ((X : PowerSeries ℚ) ^ n)
    (rescale (-1 : ℚ)
      (binomialSeries ℚ (-(ArithmeticFunction.moebius n : ℚ) / (n : ℚ))))

private noncomputable abbrev eulerPrefix (p N : ℕ) : PowerSeries ℚ :=
  ∏ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n p), eulerFactor n

private theorem constantCoeff_eulerFactor {n : ℕ} (hn : n ≠ 0) :
    constantCoeff (eulerFactor n) = 1 := by
  simp [eulerFactor, hn, ← coeff_zero_eq_constantCoeff]

private theorem constantCoeff_eulerPrefix (p N : ℕ) :
    constantCoeff (eulerPrefix p N) = 1 := by
  classical
  rw [eulerPrefix, map_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact constantCoeff_eulerFactor
    (Nat.ne_zero_of_lt (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1)

private theorem isUnit_eulerPrefix (p N : ℕ) : IsUnit (eulerPrefix p N) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_eulerPrefix]
  exact isUnit_one

private theorem coeff_eulerFactor_of_pos_of_lt {n j : ℕ} (hj : 0 < j) (hjn : j < n) :
    coeff j (eulerFactor n) = 0 := by
  rw [eulerFactor, coeff_subst_X_pow (Nat.ne_zero_of_lt hjn)]
  simp [Nat.not_dvd_of_pos_of_lt hj hjn]

private theorem le_order_one_sub_eulerFactor {n : ℕ} (hn : n ≠ 0) :
    (n : ℕ∞) ≤ order (1 - eulerFactor n) := by
  apply nat_le_order
  intro j hj
  rw [map_sub]
  rcases eq_or_ne j 0 with rfl | hj0
  · simp [coeff_zero_eq_constantCoeff, constantCoeff_eulerFactor hn]
  · simp [hj0, coeff_eulerFactor_of_pos_of_lt (Nat.pos_of_ne_zero hj0) hj]

private theorem coeff_eulerPrefix_eq (p k N : ℕ) (hN : k ≤ N) :
    coeff k (eulerPrefix p N) = coeff k (eulerPrefix p k) := by
  classical
  let s (M : ℕ) := (Finset.Icc 1 M).filter (fun n => Nat.Coprime n p)
  have hsub : s k ⊆ s N := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi, hip⟩
    rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1, hik.trans hN⟩, hip⟩
  have htail : ∀ i ∈ s N \ s k, (k : ℕ∞) < order (1 - eulerFactor i) := by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hiN, hik⟩
    rcases Finset.mem_filter.mp hiN with ⟨hiN, hip⟩
    have hi1 := (Finset.mem_Icc.mp hiN).1
    have hki : k < i := by
      by_contra h
      exact hik (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi1, Nat.le_of_not_gt h⟩, hip⟩)
    exact lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr hki)
      (le_order_one_sub_eulerFactor (Nat.ne_zero_of_lt hi1))
  calc
    coeff k (eulerPrefix p N) =
        coeff k (eulerPrefix p k * ∏ i ∈ s N \ s k, eulerFactor i) := by
      congr 1
      simpa [eulerPrefix, s, mul_comm] using (Finset.prod_sdiff (f := eulerFactor) hsub).symm
    _ = coeff k (eulerPrefix p k) := by
      simpa only [sub_sub_cancel] using
        coeff_mul_prod_one_sub_of_lt_order k (s N \ s k) (eulerPrefix p k)
          (fun i => 1 - eulerFactor i) htail

private noncomputable def eulerSeries (p : ℕ) : PowerSeries ℚ :=
  mk fun k => coeff k (eulerPrefix p k)

private theorem coeff_eulerSeries (p k : ℕ) :
    coeff k (eulerSeries p) = coeff k (eulerPrefix p k) := by
  simp [eulerSeries]

private theorem coeff_eulerSeries_eq_prefix (p k N : ℕ) (hN : k ≤ N) :
    coeff k (eulerSeries p) = coeff k (eulerPrefix p N) := by
  rw [coeff_eulerSeries]
  exact (coeff_eulerPrefix_eq p k N hN).symm

private theorem constantCoeff_eulerSeries (p : ℕ) : constantCoeff (eulerSeries p) = 1 := by
  have h : coeff 0 (eulerPrefix p 0) = 1 := by
    simpa only [coeff_zero_eq_constantCoeff] using constantCoeff_eulerPrefix p 0
  simpa only [coeff_zero_eq_constantCoeff] using (coeff_eulerSeries p 0).trans h

private theorem derivative_subst_binomialSeries_mul {R : Type*} [CommRing R]
    [Algebra ℚ R] (a : ℚ) {g : PowerSeries R} (hg : HasSubst g) :
    derivative (subst g (binomialSeries R a)) * (1 + g) =
      C (algebraMap ℚ R a) * subst g (binomialSeries R a) * derivative g := by
  have h := congrArg (substAlgHom hg)
    (derivative_binomialSeries_mul_one_add_X (A := R) a)
  simp only [map_mul, map_add, map_one] at h
  simp only [coe_substAlgHom, subst_X hg, subst_C] at h
  rw [derivative_subst hg]
  calc
    subst g (derivative (binomialSeries R a)) * derivative g * (1 + g) =
        (subst g (derivative (binomialSeries R a)) * (1 + g)) * derivative g := by ring
    _ = _ := by rw [h]; rfl

private theorem derivative_eulerFactor_mul (i : ℕ) (hi : 0 < i) :
    derivative (eulerFactor i) * (1 - X ^ i) =
      C (ArithmeticFunction.moebius i : ℚ) * X ^ (i - 1) * eulerFactor i := by
  have hi0 : i ≠ 0 := Nat.ne_zero_of_lt hi
  have hx : HasSubst ((X : PowerSeries ℚ) ^ i) := HasSubst.X_pow hi0
  have hneg : HasSubst (-((X : PowerSeries ℚ) ^ i)) :=
    HasSubst.of_constantCoeff_zero' (by simp [hi0])
  -- Rescaling before substitution gives `-X^i`, rather than `(-X)^i`.
  have hfactor : eulerFactor i =
      subst (-((X : PowerSeries ℚ) ^ i))
        (binomialSeries ℚ (-(ArithmeticFunction.moebius i : ℚ) / (i : ℚ))) := by
    rw [eulerFactor, rescale_eq_subst,
      subst_comp_subst_apply (HasSubst.smul_X' (-1 : ℚ)) hx,
      subst_smul hx, subst_X hx, neg_one_smul]
  rw [hfactor]
  have h := derivative_subst_binomialSeries_mul
    (-(ArithmeticFunction.moebius i : ℚ) / (i : ℚ)) hneg
  simp only [Algebra.algebraMap_self, RingHom.id_apply, map_neg, derivative_pow,
    derivative_X, mul_one, ← sub_eq_add_neg] at h
  rw [h]
  have hiQ : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hi0
  rw [← map_natCast (C : ℚ →+* PowerSeries ℚ)]
  have hcancel : (-(ArithmeticFunction.moebius i : ℚ) / (i : ℚ)) * -(i : ℚ) =
      (ArithmeticFunction.moebius i : ℚ) := by field_simp
  calc
    _ = C ((-(ArithmeticFunction.moebius i : ℚ) / (i : ℚ)) * -(i : ℚ)) *
        X ^ (i - 1) * subst (-((X : PowerSeries ℚ) ^ i))
          (binomialSeries ℚ (-(ArithmeticFunction.moebius i : ℚ) / (i : ℚ))) := by
      rw [map_mul, map_neg]
      ring
    _ = _ := by rw [hcancel]

private theorem coeff_negXLogDeriv_eulerFactor (i : ℕ) (hi : 0 < i)
    (u : (PowerSeries ℚ)ˣ) (hu : (u : PowerSeries ℚ) = eulerFactor i) (k : ℕ) :
    coeff k (negXLogDeriv u) =
      if 0 < k ∧ i ∣ k then -(ArithmeticFunction.moebius i : ℚ) else 0 := by
  have hi0 : i ≠ 0 := Nat.ne_zero_of_lt hi
  have hx : HasSubst ((X : PowerSeries ℚ) ^ i) := HasSubst.X_pow hi0
  have hlog : negXLogDeriv u * (1 - X ^ i) =
      -C (ArithmeticFunction.moebius i : ℚ) * X ^ i := by
    apply (Units.mul_left_inj u).mp
    calc
      (negXLogDeriv u * (1 - X ^ i)) * ↑u =
          (negXLogDeriv u * ↑u) * (1 - X ^ i) := by ring
      _ = (-X * derivative (eulerFactor i)) * (1 - X ^ i) := by
        rw [negXLogDeriv_mul_value, hu]
      _ = -X * (C (ArithmeticFunction.moebius i : ℚ) * X ^ (i - 1) *
          eulerFactor i) := by rw [mul_assoc, derivative_eulerFactor_mul i hi]
      _ = (-C (ArithmeticFunction.moebius i : ℚ) * X ^ i) * ↑u := by
        have hpow : (X : PowerSeries ℚ) * X ^ (i - 1) = X ^ i := by
          rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos hi]
        rw [hu]
        calc
          _ = (-C (ArithmeticFunction.moebius i : ℚ) * (X * X ^ (i - 1))) *
              eulerFactor i := by ring
          _ = _ := by rw [hpow]
  -- The substituted geometric inverse has coefficient one at every multiple of `i`.
  let G : PowerSeries ℚ := subst (X ^ i) (mk 1 : PowerSeries ℚ)
  have hG : G * (1 - X ^ i) = 1 := by
    have h := congrArg (substAlgHom hx) (mk_one_mul_one_sub_eq_one ℚ)
    simp only [map_mul, map_sub, map_one] at h
    simpa only [coe_substAlgHom, subst_X hx] using h
  have hnonzero : (1 - (X : PowerSeries ℚ) ^ i) ≠ 0 := by
    intro h
    have h0 := congrArg constantCoeff h
    simp [hi0] at h0
  have hseries : negXLogDeriv u = -C (ArithmeticFunction.moebius i : ℚ) * (G - 1) := by
    apply mul_right_cancel₀ hnonzero
    rw [hlog]
    calc
      -C (ArithmeticFunction.moebius i : ℚ) * X ^ i =
          -C (ArithmeticFunction.moebius i : ℚ) *
            (G * (1 - X ^ i) - (1 - X ^ i)) := by rw [hG]; ring
      _ = _ := by ring
  rw [hseries, neg_mul, map_neg, coeff_C_mul, map_sub]
  by_cases hk : k = 0
  · subst k
    simp [G, coeff_subst_X_pow hi0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    by_cases hd : i ∣ k <;> simp [G, coeff_subst_X_pow hi0, hk, hkpos, hd]

open Classical in
private theorem coeff_negXLogDeriv_eulerPrefix (p : ℕ) (hp : p.Prime)
    (k N : ℕ) (hN : k ≤ N) (u : (PowerSeries ℚ)ˣ)
    (hu : (u : PowerSeries ℚ) = eulerPrefix p N) :
    coeff k (negXLogDeriv u) = -(if ∃ j : ℕ, p ^ j = k then (1 : ℚ) else 0) := by
  classical
  rcases eq_or_ne k 0 with rfl | hk
  · have hpow : ¬ ∃ j : ℕ, p ^ j = 0 := by
      rintro ⟨j, hj⟩
      exact pow_ne_zero j hp.ne_zero hj
    rw [coeff_zero_negXLogDeriv, ite_eq_right hpow, neg_zero]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let s := (Finset.Icc 1 N).filter (fun i => Nat.Coprime i p)
  have hpos (i : ℕ) (hi : i ∈ s) : 0 < i :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1
  have hunit (i : ℕ) (hi : i ≠ 0) : IsUnit (eulerFactor i) := by
    rw [isUnit_iff_constantCoeff, constantCoeff_eulerFactor hi]
    exact isUnit_one
  let v (i : ℕ) : (PowerSeries ℚ)ˣ :=
    if hi : i ≠ 0 then (hunit i hi).unit else 1
  have hv (i : ℕ) (hi : i ∈ s) : (v i : PowerSeries ℚ) = eulerFactor i := by
    simp only [v, dite_eq_left (Nat.ne_zero_of_lt (hpos i hi)), IsUnit.unit_spec]
  have huprod : u = ∏ i ∈ s, v i := by
    apply Units.ext
    rw [Units.coe_prod, hu]
    change (∏ i ∈ s, eulerFactor i) = ∏ i ∈ s, (v i : PowerSeries ℚ)
    exact Finset.prod_congr rfl fun i hi => (hv i hi).symm
  have hindex : s.filter (fun i => i ∣ k) =
      k.divisors.filter (fun i => Nat.Coprime i p) := by
    ext i
    simp only [s, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hi1, hiN⟩, hip⟩, hik⟩
      exact ⟨⟨hik, hk⟩, hip⟩
    · rintro ⟨⟨hik, _⟩, hip⟩
      have hi1 : 1 ≤ i := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hik, hk⟩)
      exact ⟨⟨⟨hi1, (Nat.le_of_dvd hkpos hik).trans hN⟩, hip⟩, hik⟩
  calc
    coeff k (negXLogDeriv u) =
        ∑ i ∈ s, if i ∣ k then -(ArithmeticFunction.moebius i : ℚ) else 0 := by
      rw [huprod, negXLogDeriv_prod, map_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [coeff_negXLogDeriv_eulerFactor i (hpos i hi) (v i) (hv i hi) k]
        simp only [hkpos, true_and]
    _ = ∑ i ∈ s.filter (fun i => i ∣ k), -(ArithmeticFunction.moebius i : ℚ) :=
      (Finset.sum_filter (s := s) (fun i => i ∣ k)
        (fun i => -(ArithmeticFunction.moebius i : ℚ))).symm
    _ = -(∑ i ∈ k.divisors.filter (fun i => Nat.Coprime i p),
        (ArithmeticFunction.moebius i : ℚ)) := by rw [hindex, Finset.sum_neg_distrib]
    _ = -(if ∃ j : ℕ, p ^ j = k then (1 : ℚ) else 0) := by
      congr 1
      exact_mod_cast ArithmeticFunction.sum_moebius_divisors_coprime p hp k

private theorem eulerSeries_coeff_recurrence (p : ℕ) (hp : p.Prime) (n : ℕ) :
    (n : ℚ) * coeff n (eulerSeries p) =
      ∑ i ∈ Finset.range n, if p ^ i ≤ n then coeff (n - p ^ i) (eulerSeries p) else 0 := by
  classical
  let u : (PowerSeries ℚ)ˣ := (isUnit_eulerPrefix p n).unit
  have hu : (u : PowerSeries ℚ) = eulerPrefix p n := IsUnit.unit_spec _
  have hmul : coeff n (eulerSeries p * (X * derivative (artinHasseLog p))) =
      coeff n (eulerPrefix p n * (X * derivative (artinHasseLog p))) := by
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [coeff_eulerSeries_eq_prefix p ij.1 n
      (by have := Finset.mem_antidiagonal.mp hij; omega)]
  have hmulneg : coeff n (eulerPrefix p n * (-negXLogDeriv u)) =
      coeff n (eulerPrefix p n * (X * derivative (artinHasseLog p))) := by
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [map_neg, coeff_negXLogDeriv_eulerPrefix p hp ij.2 n
      (by have := Finset.mem_antidiagonal.mp hij; omega) u hu,
      coeff_X_mul_derivative_artinHasseLog p hp.two_le ij.2, neg_neg]
  have hder : eulerPrefix p n * (-negXLogDeriv u) =
      X * derivative (eulerPrefix p n) := by
    have h := negXLogDeriv_mul_value u
    rw [hu] at h
    calc
      eulerPrefix p n * (-negXLogDeriv u) =
          -(negXLogDeriv u * eulerPrefix p n) := by ring
      _ = -(-X * derivative (eulerPrefix p n)) := by rw [h]
      _ = _ := by ring
  have hcoeff : (n : ℚ) * coeff n (eulerPrefix p n) =
      coeff n (X * derivative (eulerPrefix p n)) := by
    cases n with
    | zero => simp
    | succ n => simp [coeff_derivative, mul_comm]
  calc
    (n : ℚ) * coeff n (eulerSeries p) = (n : ℚ) * coeff n (eulerPrefix p n) := by
      rw [coeff_eulerSeries_eq_prefix p n n le_rfl]
    _ = coeff n (X * derivative (eulerPrefix p n)) := hcoeff
    _ = coeff n (eulerPrefix p n * (-negXLogDeriv u)) := by rw [hder]
    _ = coeff n (eulerPrefix p n * (X * derivative (artinHasseLog p))) := hmulneg
    _ = coeff n (eulerSeries p * (X * derivative (artinHasseLog p))) := hmul.symm
    _ = _ := coeff_mul_X_derivative_artinHasseLog p hp.two_le (eulerSeries p) n

private theorem eulerSeries_eq_artinHasseExp (p : ℕ) (hp : p.Prime) :
    eulerSeries p = artinHasseExp p :=
  eq_artinHasseExp_of_coeff_recurrence p hp.two_le (eulerSeries p)
    (constantCoeff_eulerSeries p) (eulerSeries_coeff_recurrence p hp)

/-- For prime `p`, every finite Euler prefix with cutoff `N ≥ k` has the same
coefficient in degree `k` as the rational Artin–Hasse exponential. Each factor
is the formal binomial expansion of `(1 - X^n)^(-μ(n)/n)`, with `n` positive
and coprime to `p`; in particular, this is the exponential, not its reciprocal.
This is the coefficientwise Euler-product formula of Fesenko–Vostokov,
Chapter I, (9.1). -/
theorem coeff_artinHasseExp_eq_prod (p : ℕ) (hp : p.Prime) (k N : ℕ) (hN : k ≤ N) :
    coeff k (artinHasseExp p) =
      coeff k
        (∏ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n p),
          subst ((X : PowerSeries ℚ) ^ n)
            (rescale (-1 : ℚ)
              (binomialSeries ℚ (-(ArithmeticFunction.moebius n : ℚ) / (n : ℚ))))) := by
  change coeff k (artinHasseExp p) = coeff k (eulerPrefix p N)
  rw [← eulerSeries_eq_artinHasseExp p hp]
  exact coeff_eulerSeries_eq_prefix p k N hN

end PowerSeries
