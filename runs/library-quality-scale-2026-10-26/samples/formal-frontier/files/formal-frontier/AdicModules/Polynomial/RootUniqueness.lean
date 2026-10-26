/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Henselian

/-!
# Uniqueness of polynomial roots under unit-reflecting maps

A scalar ring homomorphism satisfying `IsLocalHom` reflects units. Two roots in the same
fiber of such a homomorphism coincide if the derivative at one root has unit image.
The source is a commutative ring; the target may be a noncommutative semiring.

This generalizes Mathlib's local-ring root equality
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`; its local case is recovered through
the residue homomorphism.
-/

@[expose] public section

universe u v

namespace Polynomial

/-- Two roots with the same image under a unit-reflecting scalar homomorphism are equal
if the image of the derivative at the first root is a unit. -/
theorem IsRoot.eq_of_map_eq {R : Type u} {S : Type v} [CommRing R] [Semiring S]
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (φ : R →+* S) [IsLocalHom φ] (hab : φ a = φ b)
    (hderiv : IsUnit (φ (f.derivative.eval a))) : a = b := by
  change f.eval a = 0 at ha
  change f.eval b = 0 at hb
  let δ : R := b - a
  have hδ : φ δ = 0 := by
    change φ (b - a) = 0
    calc
      φ (b - a) = φ (b + -a) := by rw [sub_eq_add_neg]
      _ = φ b + φ (-a) := map_add φ b (-a)
      _ = φ a + φ (-a) := by rw [hab]
      _ = φ (a + -a) := (map_add φ a (-a)).symm
      _ = 0 := by rw [add_neg_cancel, map_zero]
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add f a δ
  have hadd : a + δ = b := by
    dsimp only [δ]
    ring
  have hlinear : c * δ ^ 2 + f.derivative.eval a * δ = 0 := by
    simpa only [ha, hb, hadd, add_zero] using hc
  have hfactor : δ * (c * δ + f.derivative.eval a) = 0 := by
    calc
      δ * (c * δ + f.derivative.eval a) =
          c * δ ^ 2 + f.derivative.eval a * δ := by ring
      _ = 0 := hlinear
  have hunit : IsUnit (c * δ + f.derivative.eval a) := by
    apply IsUnit.of_map φ _
    simpa only [map_add, map_mul, hδ, mul_zero, zero_add] using hderiv
  have hzero : δ = 0 := hunit.mul_left_eq_zero.mp hfactor
  exact (sub_eq_zero.mp hzero).symm

end Polynomial
