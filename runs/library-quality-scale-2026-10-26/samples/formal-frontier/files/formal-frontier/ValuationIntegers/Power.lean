/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuedField
import AdicModules.Polynomial.Hensel
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Units

/-!
# Power neighborhoods in Henselian valued fields

A sharp valuation inequality near one gives a power root near one, assuming Henselianity
of the valuation integers. In the canonical valued topology, the image of the power map
on the group of units is open when the exponent has nonzero image in the field.

The value group may have arbitrary rank. Neither completeness nor discreteness is
assumed, and the derivative need not be a unit in the valuation integers.

## Limitations

In the openness statement the nonzero field-cast hypothesis is sufficient, not asserted
necessary: a trivially valued field has discrete topology.
The strict root inequality cannot in general be replaced by a weak inequality; over the
2-adic field, `m = 2` and `a = 5` lie on the boundary but `5` is not a square (modulo 8).

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition
  (2002), Chapter II, §1, Corollary 4 and the subsequent Remark: power neighborhoods
  for complete, and then Henselian, discrete valuation fields.
* Adic Modules' `HenselianRing.exists_root_of_eval_mem_span_derivative_sq_mul` supplies
  root lifting with an associated error and derivative-times-displacement. Its unit
  witness in the valuation integers gives the exact correction for the original valuation.
* Mathlib's `HenselianLocalRing`, valuation subrings and their integer-unit criterion,
  canonical valued-field topology and topology on units supply the objects used here.
-/

@[expose] public section

universe u v

open scoped Topology

namespace Valuation

variable {K : Type u} [Field K] {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀]

open Polynomial

/-- The strict input gives both a nonzero scaling parameter and an integral unit target. -/
private theorem power_input (v : Valuation K Γ₀) (m : ℕ) (a : K)
    (ha : v (a - 1) < v (m : K) ^ 2) :
    (m : K) ≠ 0 ∧ v a = 1 ∧ v ((1 - a) / (m : K) ^ 2) < 1 := by
  have hm : (m : K) ≠ 0 := by
    intro h
    simp [h] at ha
  have hm₀ : v (m : K) ≠ 0 := (v.ne_zero_iff).mpr hm
  have hle : v (m : K) ≤ 1 :=
    (v.mem_valuationSubring_iff _).mp (natCast_mem v.valuationSubring m)
  have herr : v (a - 1) < 1 := ha.trans_le (pow_le_one₀ zero_le hle)
  refine ⟨hm, ?_, ?_⟩
  · simpa only [map_one] using v.map_eq_of_sub_lt (x := 1) (y := a)
      (by simpa only [map_one] using herr)
  · rw [v.map_div, map_pow, v.map_sub_swap]
    exact (div_lt_one₀ (pow_pos (pos_iff_ne_zero.mpr hm₀) _)).mpr ha

/-- A sharp power-root neighborhood of one over a field whose valuation integers are
Henselian. The strict inequality already forces `(m : K) ≠ 0`, so no separate nonzero
exponent hypothesis is needed.

This strengthens Fesenko–Vostokov, II§1 Corollary 4 and its subsequent Remark: the printed
corollary assumes characteristic zero and the Remark concerns discrete valuations.
Here arbitrary valuation rank and positive characteristic with nonzero exponent cast
are allowed, and the correction has an exact valuation. The derivative may be a nonunit
in the valuation integers. -/
theorem exists_pow_eq_of_sub_one_lt_sq (v : Valuation K Γ₀)
    [HenselianLocalRing v.valuationSubring] (m : ℕ) (a : K)
    (ha : v (a - 1) < v (m : K) ^ 2) :
    ∃ b : K, b ^ m = a ∧ v b = 1 ∧
      v (b - 1) = v (a - 1) / v (m : K) ∧ v (b - 1) < v (m : K) := by
  obtain ⟨hm, hva, hc⟩ := power_input v m a ha
  let aO : v.valuationSubring := ⟨a, hva.le⟩
  let cO : v.valuationSubring := ⟨(1 - a) / (m : K) ^ 2, hc.le⟩
  let I := IsLocalRing.maximalIdeal v.valuationSubring
  let f : v.valuationSubring[X] := X ^ m - C aO
  have heval : f.eval 1 = 1 - aO := by simp [f]
  have hderiv : f.derivative.eval 1 = (m : v.valuationSubring) := by
    simp [f, derivative_X_pow]
  have hcI : cO ∈ I := v.mem_maximalIdeal_iff.mpr hc
  have herror : f.eval 1 ∈ Ideal.span {f.derivative.eval 1 ^ 2} * I := by
    rw [heval, hderiv]
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨cO, hcI, ?_⟩
    apply Subtype.ext
    change (m : K) ^ 2 * ((1 - a) / (m : K) ^ 2) = 1 - a
    exact mul_div_cancel₀ (1 - a) (pow_ne_zero 2 hm)
  obtain ⟨b, hroot, _, hassoc⟩ :=
    HenselianRing.exists_root_of_eval_mem_span_derivative_sq_mul I f 1 herror
  have hpow : b ^ m = aO := by
    apply sub_eq_zero.mp
    simpa only [f, eval_sub, eval_pow, eval_X, eval_C] using hroot.eq_zero
  -- Keep the associated unit in the valuation integers, not merely in the field.
  obtain ⟨e, he⟩ := hassoc
  have hunit : v ((e : v.valuationSubring) : K) = 1 := by
    simpa only [ValuationSubring.algebraMap_apply] using
      (Valuation.valuationSubring.integers v).one_of_isUnit e.isUnit
  rw [heval, hderiv] at he
  have heK := congrArg (fun z : v.valuationSubring => (z : K)) he
  change (1 - a) * ((e : v.valuationSubring) : K) =
    (m : K) * ((b : K) - 1) at heK
  have herr : v (a - 1) = v (m : K) * v ((b : K) - 1) := by
    simpa only [map_mul, hunit, mul_one, v.map_sub_swap 1 a] using congrArg v heK
  have hr : v (m : K) ≠ 0 := v.ne_zero_iff.mpr hm
  have heq : v ((b : K) - 1) = v (a - 1) / v (m : K) := by
    apply (eq_div_iff hr).mpr
    exact (mul_comm _ _).trans herr.symm
  have hlt : v ((b : K) - 1) < v (m : K) := by
    rw [heq]
    exact (div_lt_iff₀ (pos_iff_ne_zero.mpr hr)).mpr (by simpa only [pow_two] using ha)
  have hle : v (m : K) ≤ 1 :=
    (v.mem_valuationSubring_iff _).mp (natCast_mem v.valuationSubring m)
  refine ⟨(b : K), ?_, ?_, heq, hlt⟩
  · have hb := congrArg (fun z : v.valuationSubring => (z : K)) hpow
    change (b : K) ^ m = a at hb
    exact hb
  · simpa only [map_one] using
      v.map_eq_of_sub_lt (x := 1) (y := (b : K))
        (by simpa only [map_one] using hlt.trans_le hle)

end Valuation

namespace Valued

variable {K : Type u} [Field K] {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

/-- The image of the power map on the units of a Henselian valued field is open if the
exponent has nonzero image in the field. Both the field topology and the units topology
are the canonical ones.

This is a topological strengthening of the power-neighborhood assertion of
Fesenko–Vostokov, II§1 Corollary 4 and its subsequent Remark, allowing higher rank and
positive characteristic with nonzero exponent cast. It is not an iff: for a trivial
valuation every subgroup is open, including the zero-exponent image. -/
theorem isOpen_powMonoidHom_range [HenselianLocalRing hv.v.valuationSubring]
    (m : ℕ) (hm : (m : K) ≠ 0) :
    IsOpen ((powMonoidHom (α := Kˣ) m).range : Set Kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : Kˣ))
  have hball : {a : K | hv.v (a - 1) < hv.v (m : K) ^ 2} ∈ 𝓝 (1 : K) := by
    apply Valued.mem_nhds.mpr
    refine ⟨Units.mk0 (hv.v.restrict ((m : K) ^ 2)) ?_, ?_⟩
    · simpa only [Valuation.restrict_eq_zero_iff, ne_eq, map_eq_zero] using pow_ne_zero 2 hm
    · intro a ha
      simpa only [Units.val_mk0, ← map_pow, hv.v.restrict_lt_iff] using ha
  have hu : {a : Kˣ | hv.v ((a : K) - 1) < hv.v (m : K) ^ 2} ∈ 𝓝 (1 : Kˣ) :=
    (Units.continuous_val.continuousAt (x := (1 : Kˣ))).preimage_mem_nhds
      (t := {a : K | hv.v (a - 1) < hv.v (m : K) ^ 2}) hball
  apply Filter.mem_of_superset hu
  intro a ha
  obtain ⟨b, hb, hvb, _, _⟩ :=
    Valuation.exists_pow_eq_of_sub_one_lt_sq hv.v m (a : K) ha
  have hb₀ : b ≠ 0 := by
    intro h
    simpa only [h, map_zero, zero_ne_one] using hvb
  refine ⟨Units.mk0 b hb₀, ?_⟩
  apply Units.ext
  simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0] using hb

end Valued
