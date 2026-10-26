/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import ValuationIntegers.NumberTheory.DenominatorSupport
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Integrality of an expression in Bernoulli numbers

For every integer `n` and positive natural `k`, the rational number
`n^k * (n^k - 1) * (bernoulli k / k)` is integral over the integers.

For positive `N`, set `H = ∑ j < N, exp^j`. Iterated logarithmic derivatives of
`H` have numerators obtained from integer polynomials by the Euler derivative
`p ↦ X * p.derivative`. Evaluating at `X = 1` gives integer witnesses after
multiplication by powers of `N`. A cleared Bernoulli generating-function identity
identifies the same values by coefficient and factorial extraction. The case
`k = 1` follows from the parity of `n * (n - 1)`; zero and negative arguments
reduce to the positive case using parity and the vanishing of odd Bernoulli
numbers above index one. Mathlib's convention is `bernoulli 1 = -1/2`.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  Lemma 4.12, printed p. 117, for the statement and logarithmic-derivative method.
* Mathlib's Bernoulli-number convention and rational-integrality APIs.
-/

@[expose] public section

open scoped BigOperators

namespace Bernoulli

private noncomputable def geometricExpSeries (N : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range N, (PowerSeries.exp ℚ) ^ j

private noncomputable def geometricPolynomial (N : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range N, Polynomial.X ^ j

private noncomputable def eulerDerivative (p : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.X * p.derivative

private noncomputable def expPolynomialEval : Polynomial ℤ →ₐ[ℤ] PowerSeries ℚ :=
  Polynomial.aeval (PowerSeries.exp ℚ)

private theorem expPolynomialEval_eq_aeval_map (p : Polynomial ℤ) :
    expPolynomialEval p =
      Polynomial.aeval (PowerSeries.exp ℚ) (p.map (Int.castRingHom ℚ)) := by
  exact Polynomial.aeval_eq_aeval_map (Subsingleton.elim _ _) p (PowerSeries.exp ℚ)

private theorem derivative_expPolynomialEval (p : Polynomial ℤ) :
    PowerSeries.derivative (expPolynomialEval p) = expPolynomialEval (eulerDerivative p) := by
  simp only [expPolynomialEval_eq_aeval_map, eulerDerivative,
    Polynomial.map_X, map_mul, Polynomial.aeval_X]
  rw [Derivation.comp_aeval_eq, PowerSeries.derivative_exp]
  simp only [Polynomial.derivative_map, smul_eq_mul, mul_comm]

private theorem expPolynomialEval_geometricPolynomial (N : ℕ) :
    expPolynomialEval (geometricPolynomial N) = geometricExpSeries N := by
  simp [expPolynomialEval, geometricPolynomial, geometricExpSeries]

private theorem constantCoeff_geometricExpSeries (N : ℕ) :
    PowerSeries.constantCoeff (geometricExpSeries N) = (N : ℚ) := by
  simp [geometricExpSeries]

private theorem constantCoeff_expPolynomialEval (p : Polynomial ℤ) :
    PowerSeries.constantCoeff (expPolynomialEval p) = ((p.eval 1 : ℤ) : ℚ) := by
  simp [expPolynomialEval, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
    Polynomial.eval_eq_sum, Polynomial.sum]

/-- The index `i` represents the numerator for the `(i + 1)`-st logarithmic derivative. -/
private noncomputable def logarithmicNumerator (N : ℕ) : ℕ → Polynomial ℤ
  | 0 => eulerDerivative (geometricPolynomial N)
  | i + 1 => geometricPolynomial N * eulerDerivative (logarithmicNumerator N i) -
      (i + 1) * logarithmicNumerator N i * eulerDerivative (geometricPolynomial N)

private theorem expPolynomialEval_logarithmicNumerator (N : ℕ) (hN : 0 < N) (i : ℕ) :
    expPolynomialEval (logarithmicNumerator N i) =
      geometricExpSeries N ^ (i + 1) *
        (PowerSeries.derivative^[i])
          (PowerSeries.derivative (geometricExpSeries N) * (geometricExpSeries N)⁻¹) := by
  let f := geometricExpSeries N
  let g := PowerSeries.derivative f * f⁻¹
  have hf : PowerSeries.constantCoeff f ≠ 0 := by
    dsimp [f]
    rw [constantCoeff_geometricExpSeries]
    exact_mod_cast Nat.ne_of_gt hN
  change expPolynomialEval (logarithmicNumerator N i) =
    f ^ (i + 1) * (PowerSeries.derivative^[i]) g
  induction i with
  | zero =>
    simp only [logarithmicNumerator, ← derivative_expPolynomialEval,
      expPolynomialEval_geometricPolynomial, Nat.zero_add, pow_one, Function.iterate_zero_apply]
    change PowerSeries.derivative f = f * (PowerSeries.derivative f * f⁻¹)
    calc
      _ = PowerSeries.derivative f * (f * f⁻¹) := by
        rw [PowerSeries.mul_inv_cancel f hf, mul_one]
      _ = _ := by ring
  | succ i ih =>
    have hd := congrArg (fun s : PowerSeries ℚ => PowerSeries.derivative s) ih
    simp only [derivative_expPolynomialEval, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_pow, Nat.add_sub_cancel] at hd
    calc
      expPolynomialEval (logarithmicNumerator N (i + 1)) =
          f * expPolynomialEval (eulerDerivative (logarithmicNumerator N i)) -
            (i + 1) * expPolynomialEval (logarithmicNumerator N i) *
              PowerSeries.derivative f := by
        simp only [logarithmicNumerator, map_sub, map_mul, map_add, map_natCast, map_one,
          expPolynomialEval_geometricPolynomial, ← derivative_expPolynomialEval]
        rfl
      _ = f ^ (i + 1 + 1) * PowerSeries.derivative ((PowerSeries.derivative^[i]) g) := by
        rw [hd, ih]
        simp only [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ = f ^ (i + 1 + 1) * (PowerSeries.derivative^[i + 1]) g := by
        rw [Function.iterate_succ_apply']

private theorem exists_int_pow_mul_constantCoeff_iterate_geometricExpSeries
    (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : 0 < r) :
    ∃ z : ℤ, (N : ℚ) ^ r *
      PowerSeries.constantCoeff ((PowerSeries.derivative^[r - 1])
        (PowerSeries.derivative (geometricExpSeries N) * (geometricExpSeries N)⁻¹)) =
      (z : ℚ) := by
  cases r with
  | zero => simp at hr
  | succ i =>
    refine ⟨(logarithmicNumerator N i).eval 1, ?_⟩
    simpa only [map_mul, map_pow, constantCoeff_geometricExpSeries,
      constantCoeff_expPolynomialEval, Nat.succ_eq_add_one, Nat.add_sub_cancel] using
      (congrArg PowerSeries.constantCoeff (expPolynomialEval_logarithmicNumerator N hN i)).symm

/-- Extract the normalized Bernoulli coefficient from a cleared series identity. -/
private theorem constantCoeff_iterate_derivative_of_X_mul_eq_bernoulliPowerSeries
    (a : ℚ) (g : PowerSeries ℚ)
    (hseries : PowerSeries.X * g =
      PowerSeries.rescale a (bernoulliPowerSeries ℚ) - bernoulliPowerSeries ℚ +
        PowerSeries.C (a - 1) * PowerSeries.X)
    (k : ℕ) (hk : 1 < k) :
    PowerSeries.constantCoeff ((PowerSeries.derivative^[k - 1]) g) =
      (a ^ k - 1) * (bernoulli k / (k : ℚ)) := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hk)
  have hk1 : k ≠ 1 := ne_of_gt hk
  have hshift := PowerSeries.coeff_succ_X_mul (k - 1) g
  rw [Nat.sub_add_cancel (Nat.le_of_lt hk)] at hshift
  have hcoefficient : PowerSeries.coeff (k - 1) g =
      a ^ k * (bernoulli k / (k.factorial : ℚ)) -
        bernoulli k / (k.factorial : ℚ) := by
    have h := congrArg (PowerSeries.coeff k) hseries
    rw [hshift, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
      ite_eq_right hk1, mul_zero, add_zero] at h
    simpa [PowerSeries.coeff_rescale, bernoulliPowerSeries] using h
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hfQ : ((k - 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k - 1)
  have hfactorial : (k.factorial : ℚ) = (k : ℚ) * ((k - 1).factorial : ℚ) := by
    exact_mod_cast (Nat.mul_factorial_pred hk0).symm
  rw [PowerSeries.constantCoeff_iterate_derivative, hcoefficient, hfactorial]
  field_simp [hkQ, hfQ]

private theorem geometricExpSeries_mul_exp_sub_one (N : ℕ) :
    geometricExpSeries N * (PowerSeries.exp ℚ - 1) = PowerSeries.exp ℚ ^ N - 1 := by
  exact geom_sum_mul (PowerSeries.exp ℚ) N

private theorem rescale_bernoulliPowerSeries_mul_exp_pow_sub_one (N : ℕ) :
    PowerSeries.rescale (N : ℚ) (bernoulliPowerSeries ℚ) *
      (PowerSeries.exp ℚ ^ N - 1) = PowerSeries.C (N : ℚ) * PowerSeries.X := by
  simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X,
    ← PowerSeries.exp_pow_eq_rescale_exp] using
      congrArg (PowerSeries.rescale (N : ℚ)) (bernoulliPowerSeries_mul_exp_sub_one ℚ)

private theorem geometricExpSeries_mul_rescale_bernoulliPowerSeries (N : ℕ) :
    geometricExpSeries N * PowerSeries.rescale (N : ℚ) (bernoulliPowerSeries ℚ) =
      PowerSeries.C (N : ℚ) * bernoulliPowerSeries ℚ := by
  have hexp : PowerSeries.exp ℚ - 1 ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) h
    norm_num at hc
  apply (mul_right_inj' hexp).mp
  calc
    _ = PowerSeries.rescale (N : ℚ) (bernoulliPowerSeries ℚ) *
        (geometricExpSeries N * (PowerSeries.exp ℚ - 1)) := by ring
    _ = PowerSeries.C (N : ℚ) * PowerSeries.X := by
      rw [geometricExpSeries_mul_exp_sub_one,
        rescale_bernoulliPowerSeries_mul_exp_pow_sub_one]
    _ = PowerSeries.C (N : ℚ) *
        (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) := by
      rw [bernoulliPowerSeries_mul_exp_sub_one]
    _ = _ := by ring

/-- The logarithmic derivative of the finite exponential sum, with its pole cleared by `X`. -/
private theorem X_mul_logarithmicDerivative_geometricExpSeries (N : ℕ) (hN : 0 < N) :
    PowerSeries.X * (PowerSeries.derivative (geometricExpSeries N) *
      (geometricExpSeries N)⁻¹) =
      PowerSeries.rescale (N : ℚ) (bernoulliPowerSeries ℚ) - bernoulliPowerSeries ℚ +
        PowerSeries.C ((N : ℚ) - 1) * PowerSeries.X := by
  let H := geometricExpSeries N
  let E := PowerSeries.exp ℚ
  let B := bernoulliPowerSeries ℚ
  let B_N := PowerSeries.rescale (N : ℚ) B
  let c := PowerSeries.C (N : ℚ)
  have hgeom : H * (E - 1) = E ^ N - 1 := geometricExpSeries_mul_exp_sub_one N
  have hB : B * (E - 1) = PowerSeries.X := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have hHB : H * B_N = c * B := geometricExpSeries_mul_rescale_bernoulliPowerSeries N
  have hpow : PowerSeries.derivative (E ^ N) = c * E ^ N := by
    dsimp [E, c]
    rw [map_natCast, PowerSeries.derivative_pow, PowerSeries.derivative_exp,
      mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt hN)]
  have hE : PowerSeries.derivative E = E := PowerSeries.derivative_exp ℚ
  have hd := congrArg (fun s : PowerSeries ℚ => PowerSeries.derivative s) hgeom
  simp only [map_sub, Derivation.leibniz, smul_eq_mul, hE,
    PowerSeries.derivative_one, sub_zero, hpow] at hd
  have heN : E ^ N = H * (E - 1) + 1 := by rw [hgeom]; ring
  have hclear : PowerSeries.X * PowerSeries.derivative H =
      H * (B_N - B + PowerSeries.C ((N : ℚ) - 1) * PowerSeries.X) := by
    calc
      _ = B * (PowerSeries.derivative H * (E - 1)) := by rw [← hB]; ring
      _ = B * (c * E ^ N - H * E) := by rw [← hd]; ring
      _ = c * H * (B * (E - 1)) + c * B - H * (B * (E - 1)) - H * B := by
        rw [heN]
        ring
      _ = H * B_N - H * B + (c - 1) * H * PowerSeries.X := by rw [hB, hHB]; ring
      _ = _ := by dsimp [c]; rw [map_sub, map_one]; ring
  have hf : PowerSeries.constantCoeff H ≠ 0 := by
    dsimp [H]
    rw [constantCoeff_geometricExpSeries]
    exact_mod_cast Nat.ne_of_gt hN
  change PowerSeries.X * (PowerSeries.derivative H * H⁻¹) =
    B_N - B + PowerSeries.C ((N : ℚ) - 1) * PowerSeries.X
  calc
    _ = (PowerSeries.X * PowerSeries.derivative H) * H⁻¹ := by ring
    _ = (B_N - B + PowerSeries.C ((N : ℚ) - 1) * PowerSeries.X) * (H * H⁻¹) := by
      rw [hclear]
      ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel H hf, mul_one]

/-- The index-one expression has an integer witness for every integer argument. -/
private theorem isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div_one (n : ℤ) :
    IsIntegral ℤ ((n : ℚ) ^ 1 * ((n : ℚ) ^ 1 - 1) *
      (bernoulli 1 / (1 : ℚ))) := by
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self n
  have hmQ : (n : ℚ) * ((n : ℚ) - 1) = (m : ℚ) + (m : ℚ) := by
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_add] using
      congrArg (fun z : ℤ => (z : ℚ)) hm
  have hvalue : (n : ℚ) ^ 1 * ((n : ℚ) ^ 1 - 1) *
      (bernoulli 1 / (1 : ℚ)) = ((-m : ℤ) : ℚ) := by
    simp only [pow_one, bernoulli_one, div_one, Int.cast_neg]
    rw [hmQ]
    ring
  rw [hvalue]
  exact isIntegral_intCast (-m)

/-- Extend integrality from positive natural arguments and indices greater than one
using the index-one formula, parity and vanishing of odd Bernoulli numbers. -/
private theorem isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div_of_pos_nat
    (hpos : ∀ (N : ℕ), 0 < N → ∀ (k : ℕ), 1 < k →
      IsIntegral ℤ ((N : ℚ) ^ k * ((N : ℚ) ^ k - 1) *
        (bernoulli k / (k : ℚ))))
    (n : ℤ) (k : ℕ) (hk : 0 < k) :
    IsIntegral ℤ ((n : ℚ) ^ k * ((n : ℚ) ^ k - 1) *
      (bernoulli k / (k : ℚ))) := by
  by_cases hk1 : k = 1
  · subst k
    exact isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div_one n
  have hk2 : 1 < k := lt_of_le_of_ne (Nat.succ_le_of_lt hk) (Ne.symm hk1)
  by_cases hn0 : n = 0
  · subst n
    simp only [Int.cast_zero, zero_pow (Nat.ne_of_gt hk), zero_mul]
    exact isIntegral_intCast 0
  by_cases hn1 : n = 1
  · subst n
    simp only [Int.cast_one, one_pow, sub_self, mul_zero, zero_mul]
    exact isIntegral_intCast 0
  cases n with
  | ofNat N =>
      have hN : 0 < N := by
        apply Nat.pos_of_ne_zero
        intro hN
        apply hn0
        subst N
        rfl
      simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hpos N hN k hk2
  | negSucc N =>
      rcases Nat.even_or_odd k with heven | hodd
      · simpa only [Int.cast_negSucc, heven.neg_pow] using
          hpos (N + 1) (Nat.succ_pos N) k hk2
      · rw [bernoulli_eq_zero_of_odd hodd hk2, zero_div, mul_zero]
        exact isIntegral_intCast 0

/-- For an integer `n` and positive natural `k`, the rational number
`n^k * (n^k - 1) * (bernoulli k / k)` is integral over the integers.
This is Hatcher's *Vector Bundles and K-Theory*, Lemma 4.12, with `bernoulli 1 = -1/2`.
-/
theorem isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div
    (n : ℤ) (k : ℕ) (hk : 0 < k) :
    IsIntegral ℤ ((n : ℚ) ^ k * ((n : ℚ) ^ k - 1) *
      (bernoulli k / (k : ℚ))) := by
  refine isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div_of_pos_nat ?_ n k hk
  intro N hN r hr
  obtain ⟨z, hz⟩ := exists_int_pow_mul_constantCoeff_iterate_geometricExpSeries N hN r
    (lt_trans Nat.zero_lt_one hr)
  have hcoefficient := constantCoeff_iterate_derivative_of_X_mul_eq_bernoulliPowerSeries
    (N : ℚ) (PowerSeries.derivative (geometricExpSeries N) * (geometricExpSeries N)⁻¹)
    (X_mul_logarithmicDerivative_geometricExpSeries N hN) r hr
  rw [hcoefficient, ← mul_assoc] at hz
  rw [hz]
  exact isIntegral_intCast z

/-- Every prime in the reduced denominator of `bernoulli k / k` satisfies
`p - 1 ∣ k`. For positive `k`, use the integrality of
`n^k * (n^k - 1) * (bernoulli k / k)` from Hatcher's *Vector Bundles and K-Theory*,
Lemma 4.12, and the prime-cancellation argument following that lemma in the proof
of Theorem 4.9 (§4.1). At `k = 0`, the conclusion holds because every natural
number divides zero.
The statement includes index one, with `bernoulli 1 = -1/2`, and odd indices
above one, where the quotient is zero. -/
theorem sub_one_dvd_of_dvd_den_bernoulli_div
    (k p : ℕ) (hp : p.Prime)
    (hden : p ∣ (bernoulli k / (k : ℚ)).den) : p - 1 ∣ k := by
  cases k with
  | zero => exact dvd_zero _
  | succ k =>
    refine Rat.sub_one_dvd_of_dvd_den_of_forall_isIntegral_pow_mul_pow_sub_one_mul
      (bernoulli k.succ / (k.succ : ℚ)) k.succ p hp ?_ hden
    intro n
    simpa only [Int.cast_natCast] using
      isIntegral_pow_mul_pow_sub_one_mul_bernoulli_div (n : ℤ) k.succ (Nat.succ_pos k)

end Bernoulli
