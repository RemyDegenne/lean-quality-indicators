/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.NonUnitalNilpotent
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Units over a square-zero kernel

For a ring homomorphism `f` with square-zero kernel, the units mapping to `1`
are identified with the additive kernel, written multiplicatively. The forward
map subtracts `1`; the inverse uses the explicit nilpotent unit with value `1 + x`.
Square-zero means that every product of two kernel elements vanishes, not merely
that each individual element has square zero.

The domain ring may be noncommutative, and the codomain is only a semiring.
Neither surjectivity nor nontriviality is required. The construction uses the
explicit finite geometric-series unit from `GeneralLinearGroups.NonUnitalNilpotent`.

## References

The first-order multiplication identity is the algebraic ingredient in
Fesenko and Vostokov, *Local Fields and Their Extensions*, second edition,
Chapter I, (5.4)(3). Here it is formulated for arbitrary homomorphisms rather
than only successive layers in a valuation-ring unit filtration. Ideals,
unit groups and multiplicative type tags are from Mathlib.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [Ring R] [Semiring S]

private theorem unitsKer_sub_one_mem (f : R →+* S)
    (u : (Units.map f.toMonoidHom).ker) : (u.1 : R) - 1 ∈ ker f := by
  have hu : f (u.1 : R) = 1 := congrArg Units.val u.property
  change f ((u.1 : R) - 1) = 0
  calc
    f ((u.1 : R) - 1) = f (u.1 : R) + f (-1) := by rw [sub_eq_add_neg, map_add]
    _ = f 1 + f (-1) := by rw [hu, map_one]
    _ = f (1 + -1) := (map_add f _ _).symm
    _ = 0 := by simp

/-- The units in the kernel of the unit map of a ring homomorphism with
square-zero kernel, identified with its additive kernel. The maps are
`u ↦ u - 1` and `x ↦ 1 + x`. The latter is a unit because the whole kernel
has square zero. This is the algebraic first-order unit-layer construction
underlying Fesenko–Vostokov, Chapter I, (5.4)(3). -/
def unitsKerEquivOfSquareZero (f : R →+* S) (hker : ker f ^ 2 = ⊥) :
    (Units.map f.toMonoidHom).ker ≃* Multiplicative (ker f) where
  toFun u := Multiplicative.ofAdd ⟨(u.1 : R) - 1, by exact unitsKer_sub_one_mem f u⟩
  invFun x :=
    ⟨IsNilpotent.oneAddUnitOfPowEqZero ((Multiplicative.toAdd x : ker f) : R) 2
      (by
        have hx := Ideal.pow_mem_pow (Multiplicative.toAdd x).property 2
        rw [hker] at hx
        exact Ideal.mem_bot.mp hx), by
      apply Units.ext
      change f (1 + ((Multiplicative.toAdd x : ker f) : R)) = 1
      rw [map_add, map_one, mem_ker.mp (Multiplicative.toAdd x).property, add_zero]⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    change 1 + ((u.1 : R) - 1) = (u.1 : R)
    abel
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (1 + ((Multiplicative.toAdd x : ker f) : R)) - 1 = _
    abel
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (u.1 : R) * (v.1 : R) - 1 = ((u.1 : R) - 1) + ((v.1 : R) - 1)
    have hxy := Ideal.mul_mem_mul (unitsKer_sub_one_mem f u) (unitsKer_sub_one_mem f v)
    have hker' := hker
    rw [Submodule.pow_succ, Submodule.pow_one] at hker'
    rw [hker', Ideal.mem_bot] at hxy
    rw [sub_mul, mul_sub, one_mul, mul_one] at hxy
    calc
      (u.1 : R) * (v.1 : R) - 1 =
          (((u.1 : R) * (v.1 : R) - (u.1 : R)) - ((v.1 : R) - 1)) +
            (((u.1 : R) - 1) + ((v.1 : R) - 1)) := by abel
      _ = _ := by rw [hxy, zero_add]

/-- The forward coordinate is the value of the unit minus `1`. -/
@[simp]
theorem unitsKerEquivOfSquareZero_apply_coe (f : R →+* S)
    (hker : ker f ^ 2 = ⊥) (u : (Units.map f.toMonoidHom).ker) :
    ((Multiplicative.toAdd (unitsKerEquivOfSquareZero f hker u) : ker f) : R) =
      (u.1 : R) - 1 := rfl

/-- The inverse coordinate has value `1 + x`. -/
@[simp]
theorem unitsKerEquivOfSquareZero_symm_apply_coe (f : R →+* S)
    (hker : ker f ^ 2 = ⊥) (x : Multiplicative (ker f)) :
    (((unitsKerEquivOfSquareZero f hker).symm x).1 : R) =
      1 + ((Multiplicative.toAdd x : ker f) : R) := rfl

/-- The inverse of the unit associated to `x` has value `1 - x`. -/
@[simp]
theorem unitsKerEquivOfSquareZero_symm_apply_inv_coe (f : R →+* S)
    (hker : ker f ^ 2 = ⊥) (x : Multiplicative (ker f)) :
    Units.val ((((unitsKerEquivOfSquareZero f hker).symm x).1)⁻¹) =
      1 - ((Multiplicative.toAdd x : ker f) : R) := by
  change (∑ i ∈ Finset.range 2, (-((Multiplicative.toAdd x : ker f) : R)) ^ i) = _
  simp [Finset.sum_range_succ, sub_eq_add_neg]

end RingHom
