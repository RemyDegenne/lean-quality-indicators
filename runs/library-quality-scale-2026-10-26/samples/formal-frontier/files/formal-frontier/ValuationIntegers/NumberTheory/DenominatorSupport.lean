/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Prime support of rational denominators

If `n^k * (n^k - 1) * q` is integral over the integers for every natural `n`,
then every prime `p` in the reduced denominator of `q` satisfies `p - 1 ∣ k`.
The exponent `k` may be zero: the integrality condition then holds for every
rational `q`, and every natural number divides zero.

The arithmetic criterion generalizes Hatcher's prime-cancellation argument in
the proof of Theorem 4.9, following Lemma 4.12, to an arbitrary rational
coefficient. It relates integrality to the exponent of the cyclic group of units
modulo a prime.

## References

* Allen Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
  §4.1, proof of Theorem 4.9, argument following Lemma 4.12.
* Mathlib's rational-integrality, finite-domain cyclicity and group-exponent APIs.
-/

@[expose] public section

namespace Rat

/-- If `n^k * (n^k - 1) * q` is integral over the integers for every natural
`n`, a prime dividing the reduced denominator of `q` has `p - 1 ∣ k`.

This generalizes Hatcher's prime-cancellation argument following Lemma 4.12 in
§4.1 of *Vector Bundles and K-Theory* (proof of Theorem 4.9), with an arbitrary
rational coefficient in place of the divided Bernoulli coefficient. The case
`k = 0` is included: the integrality condition and divisibility conclusion are
then automatic. -/
theorem sub_one_dvd_of_dvd_den_of_forall_isIntegral_pow_mul_pow_sub_one_mul
    (q : ℚ) (k p : ℕ) (hp : p.Prime)
    (hint : ∀ n : ℕ, IsIntegral ℤ ((n : ℚ) ^ k * ((n : ℚ) ^ k - 1) * q))
    (hden : p ∣ q.den) : p - 1 ∣ k := by
  let : Fact p.Prime := ⟨hp⟩
  have hnum : (q.num : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ q.num.natAbs :=
      Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd q.num p).mp hzero)
    have hcoprime : p.Coprime q.num.natAbs :=
      q.reduced.symm.coprime_dvd_left hden
    exact (hp.coprime_iff_not_dvd.mp hcoprime) hdiv
  have hmod (n : ℕ) : (n : ZMod p) ^ k * ((n : ZMod p) ^ k - 1) = 0 := by
    -- Clear the rational denominator in characteristic zero before reducing modulo `p`.
    obtain ⟨z, hz⟩ := UniqueFactorizationMonoid.integer_of_integral (hint n)
    change (z : ℚ) = (n : ℚ) ^ k * ((n : ℚ) ^ k - 1) * q at hz
    have hclear : z * (q.den : ℤ) = (n : ℤ) ^ k * ((n : ℤ) ^ k - 1) * q.num := by
      apply Int.cast_injective (α := ℚ)
      simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_sub, Int.cast_one]
      rw [hz, mul_assoc, Rat.mul_den_eq_num]
    have hden_zero : (q.den : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff q.den p).mpr hden
    have hreduce := congrArg (fun a : ℤ => (a : ZMod p)) hclear
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_sub, Int.cast_one,
      hden_zero, mul_zero] at hreduce
    exact (mul_eq_zero.mp hreduce.symm).resolve_right hnum
  have hexponent : Monoid.exponent (ZMod p)ˣ ∣ k := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro u
    apply Units.ext
    have h := hmod (u : ZMod p).val
    rw [ZMod.natCast_val, ZMod.cast_id] at h
    have hpow : (u : ZMod p) ^ k - 1 = 0 :=
      (mul_eq_zero.mp h).resolve_left (pow_ne_zero k u.ne_zero)
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using sub_eq_zero.mp hpow
  rwa [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units p] at hexponent

end Rat
