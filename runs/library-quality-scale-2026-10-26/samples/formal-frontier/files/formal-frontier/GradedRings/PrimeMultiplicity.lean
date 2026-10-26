/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# Prime-multiplicity valuations

This file packages the multiplicity of a prime element in a domain with
well-founded divisibility as an integer-valued valuation.  Unlike the
`ℕ∞`-valued additive valuation `multiplicity_addValuation`, this valuation has
a group-valued nonzero part and therefore extends across localizations.
-/

@[expose] public section

open Multiplicative WithZero

noncomputable section

namespace PrimeMultiplicity

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]
variable {p : R}

/-- The multiplicative value attached to prime multiplicity on the original
domain.  A nonzero element `r` is sent to `exp (-multiplicity p r)`. -/
noncomputable def valuationDef (p r : R) : ℤᵐ⁰ :=
  by
    classical
    exact if r = 0 then 0 else exp (-(multiplicity p r : ℤ))

omit [IsDomain R] [WfDvdMonoid R] in
@[simp]
theorem valuationDef_zero (p : R) : valuationDef p 0 = 0 := by
  simp [valuationDef]

omit [WfDvdMonoid R] in
@[simp]
theorem valuationDef_one (hp : Prime p) : valuationDef p 1 = 1 := by
  rw [valuationDef]
  simp only [ite_false, one_ne_zero, multiplicity_of_one_right hp.not_isUnit,
    Nat.cast_zero, neg_zero, exp_zero]

omit [IsDomain R] [WfDvdMonoid R] in
theorem valuationDef_of_ne_zero (p : R) {r : R} (hr : r ≠ 0) :
    valuationDef p r = exp (-(multiplicity p r : ℤ)) := by
  simp [valuationDef, hr]

omit [WfDvdMonoid R] in
/-- A prime power has multiplicity equal to its exponent. This is the
simp-normal-form computation rule after `valuation_apply` unfolds the bundled
valuation. -/
@[simp]
theorem valuationDef_pow (hp : Prime p) (n : ℕ) :
    valuationDef p (p ^ n) = exp (-(n : ℤ)) := by
  rw [valuationDef_of_ne_zero p (pow_ne_zero n hp.ne_zero),
    multiplicity_pow_self_of_prime hp]

theorem valuationDef_mul (hp : Prime p) (x y : R) :
    valuationDef p (x * y) = valuationDef p x * valuationDef p y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hfin : FiniteMultiplicity p (x * y) :=
    FiniteMultiplicity.of_prime_left hp hxy
  rw [valuationDef_of_ne_zero p hxy, valuationDef_of_ne_zero p hx,
    valuationDef_of_ne_zero p hy, multiplicity_mul hp hfin]
  simp only [Nat.cast_add, neg_add_rev, exp_add, mul_comm]

theorem min_multiplicity_le_multiplicity_add (hp : Prime p)
    {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (multiplicity p x) (multiplicity p y) ≤ multiplicity p (x + y) := by
  have hxfin : FiniteMultiplicity p x := FiniteMultiplicity.of_prime_left hp hx
  have hyfin : FiniteMultiplicity p y := FiniteMultiplicity.of_prime_left hp hy
  have hxyfin : FiniteMultiplicity p (x + y) :=
    FiniteMultiplicity.of_prime_left hp hxy
  have h := min_le_emultiplicity_add (p := p) (a := x) (b := y)
  simpa [hxfin.emultiplicity_eq_multiplicity,
    hyfin.emultiplicity_eq_multiplicity,
    hxyfin.emultiplicity_eq_multiplicity] using h

theorem valuationDef_add_le_max (hp : Prime p) (x y : R) :
    valuationDef p (x + y) ≤ max (valuationDef p x) (valuationDef p y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  by_cases hxy : x + y = 0
  · simp [valuationDef_zero, hxy]
  rw [valuationDef_of_ne_zero p hxy, valuationDef_of_ne_zero p hx,
    valuationDef_of_ne_zero p hy, le_max_iff]
  simp only [exp_le_exp, neg_le_neg_iff, Nat.cast_le, ← min_le_iff]
  exact min_multiplicity_le_multiplicity_add hp hx hy hxy

/-- The integer-valued multiplicative valuation associated to a prime element
in a domain with well-founded divisibility. -/
noncomputable def valuation (hp : Prime p) : Valuation R ℤᵐ⁰ where
  toFun := valuationDef p
  map_zero' := valuationDef_zero p
  map_one' := valuationDef_one hp
  map_mul' := valuationDef_mul hp
  map_add_le_max' := valuationDef_add_le_max hp

@[simp]
theorem valuation_apply (hp : Prime p) (r : R) :
    valuation hp r = valuationDef p r :=
  rfl

theorem valuation_apply_of_ne_zero (hp : Prime p) {r : R} (hr : r ≠ 0) :
    valuation hp r = exp (-(multiplicity p r : ℤ)) :=
  valuationDef_of_ne_zero p hr

theorem valuation_apply_pow (hp : Prime p) (n : ℕ) :
    valuation hp (p ^ n) = exp (-(n : ℤ)) := by
  rw [valuation_apply_of_ne_zero hp (pow_ne_zero n hp.ne_zero),
    multiplicity_pow_self_of_prime hp]

theorem valuation_ne_zero (hp : Prime p) {r : R} (hr : r ≠ 0) :
    valuation hp r ≠ 0 := by
  rw [valuation_apply_of_ne_zero hp hr]
  exact WithZero.coe_ne_zero

variable {S : Submonoid R} {B : Type*} [CommRing B] [Algebra R B]
  [IsLocalization S B]

/-- Extend prime multiplicity to a localization whose denominators are
non-zero-divisors. -/
noncomputable def localizationValuation (hp : Prime p)
    (hS : S ≤ nonZeroDivisors R) : Valuation B ℤᵐ⁰ :=
  (valuation hp).extendToLocalization (S := S) (B := B) (by
    intro s hs
    change s ∉ (valuation hp).supp
    rw [Valuation.mem_supp_iff]
    exact valuation_ne_zero hp (nonZeroDivisors.coe_ne_zero ⟨s, hS hs⟩))

@[simp]
theorem localizationValuation_mk' (hp : Prime p)
    (hS : S ≤ nonZeroDivisors R) (x : R) (y : S) :
    localizationValuation (B := B) hp hS (IsLocalization.mk' B x y) =
      valuation hp x * (valuation hp y)⁻¹ := by
  unfold localizationValuation
  rw [Valuation.extendToLocalization_mk']

omit [WfDvdMonoid R] in
theorem powers_le_nonZeroDivisors (hp : Prime p) :
    Submonoid.powers p ≤ nonZeroDivisors R := by
  rintro _ ⟨n, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact pow_ne_zero n hp.ne_zero

/-- The prime-multiplicity valuation on a localization away from the prime. -/
noncomputable def awayValuation (hp : Prime p) {B : Type*} [CommRing B]
    [Algebra R B] [IsLocalization.Away p B] : Valuation B ℤᵐ⁰ :=
  localizationValuation hp (powers_le_nonZeroDivisors hp)

@[simp]
theorem awayValuation_mk' (hp : Prime p) {B : Type*} [CommRing B]
    [Algebra R B] [IsLocalization.Away p B] (x : R)
    (y : Submonoid.powers p) :
    awayValuation (B := B) hp (IsLocalization.mk' B x y) =
      valuation hp x * (valuation hp y)⁻¹ := by
  exact localizationValuation_mk' hp (powers_le_nonZeroDivisors hp) x y

theorem awayValuation_mk_pow_of_ne_zero (hp : Prime p) {B : Type*}
    [CommRing B] [Algebra R B] [IsLocalization.Away p B]
    (x : R) (hx : x ≠ 0) (n : ℕ) :
    awayValuation (B := B) hp
        (IsLocalization.mk' (M := Submonoid.powers p) B x
          ⟨p ^ n, ⟨n, rfl⟩⟩) =
      exp ((n : ℤ) - multiplicity p x) := by
  rw [awayValuation_mk', valuation_apply_of_ne_zero hp hx,
    valuation_apply_pow]
  simp only [inv_exp, ← exp_add]
  congr 1
  ring

end PrimeMultiplicity
