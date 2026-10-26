/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.ZeroProductStabilization
public import Mathlib.LinearAlgebra.Matrix.Invertible

/-!
# Switching rectangular unit products

Over an arbitrary ring, a unit with matrix `1 + A * B` determines a unit with
matrix `1 + B * A`. Its inverse is read back through the ordered product
`1 - B * (1 + A * B)⁻¹ * A`. The diagonal pair of the original unit and the
inverse switched unit admits an ordered factorization into four rectangular
elementary shears. Empty blocks and the zero ring are permitted.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR} [Ring R]

/-- Switch the rectangular factors of a unit represented by `1 + A * B`. -/
def rectangularUnitSwitch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) : GL Y R := by
  letI : Invertible (1 + A * B : Matrix X X R) := hg ▸ g.invertible
  letI : Invertible (1 : Matrix X X R) := invertibleOne
  letI : Invertible (1 : Matrix Y Y R) := invertibleOne
  letI : Invertible (⅟(1 : Matrix X X R) + A * ⅟(1 : Matrix Y Y R) * B) := by
    simpa only [invOf_one, Matrix.one_mul, Matrix.mul_one] using
      (inferInstance : Invertible (1 + A * B : Matrix X X R))
  letI : Invertible (1 + B * A : Matrix Y Y R) := by
    simpa only [Matrix.mul_one] using
      (Matrix.invertibleAddMulMul (1 : Matrix Y Y R) B (1 : Matrix X X R) A)
  exact unitOfInvertible (1 + B * A)

/-- The switched unit has matrix `1 + B * A`. -/
@[simp]
theorem rectangularUnitSwitch_val (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    (rectangularUnitSwitch A B g hg : Matrix Y Y R) = 1 + B * A := rfl

/-- The inverse switched unit has the ordered inverse from the matrix Woodbury identity. -/
@[simp]
theorem rectangularUnitSwitch_inv_val (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    (((rectangularUnitSwitch A B g hg)⁻¹ : GL Y R) : Matrix Y Y R) =
      1 - B * ((g⁻¹ : GL X R) : Matrix X X R) * A := by
  let : Invertible (1 + A * B : Matrix X X R) := hg ▸ g.invertible
  let : Invertible (1 : Matrix X X R) := invertibleOne
  let : Invertible (1 : Matrix Y Y R) := invertibleOne
  let : Invertible (⅟(1 : Matrix X X R) + A * ⅟(1 : Matrix Y Y R) * B) := by
    simpa only [invOf_one, Matrix.one_mul, Matrix.mul_one] using
      (inferInstance : Invertible (1 + A * B : Matrix X X R))
  let : Invertible (1 + B * A : Matrix Y Y R) := by
    simpa only [Matrix.mul_one] using
      (Matrix.invertibleAddMulMul (1 : Matrix Y Y R) B (1 : Matrix X X R) A)
  let : Invertible (1 + B * (1 : Matrix X X R) * A : Matrix Y Y R) :=
    Matrix.invertibleAddMulMul (1 : Matrix Y Y R) B (1 : Matrix X X R) A
  have hwoodbury : ⅟(1 + B * A : Matrix Y Y R) =
      1 - B * ⅟(1 + A * B : Matrix X X R) * A := by
    simpa only [invOf_one, Matrix.one_mul, Matrix.mul_one] using
      (Matrix.invOf_add_mul_mul (1 : Matrix Y Y R) B (1 : Matrix X X R) A)
  have hinv : ⅟(1 + A * B : Matrix X X R) =
      ((g⁻¹ : GL X R) : Matrix X X R) := by
    let : Invertible (g : Matrix X X R) := g.invertible
    calc
      ⅟(1 + A * B : Matrix X X R) = ⅟(g : Matrix X X R) :=
        invertible_unique (1 + A * B : Matrix X X R) (g : Matrix X X R) hg.symm
      _ = ((g⁻¹ : GL X R) : Matrix X X R) := invOf_units g
  change ⅟(1 + B * A : Matrix Y Y R) = _
  rw [hwoodbury, hinv]

/-- The switched unit is uniquely characterized by its matrix value. -/
theorem eq_rectangularUnitSwitch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B)
    (h : GL Y R) (hh : (h : Matrix Y Y R) = 1 + B * A) :
    h = rectangularUnitSwitch A B g hg := by
  apply Units.ext
  rw [hh, rectangularUnitSwitch_val]

/-- Switching the factors twice recovers the original unit. -/
@[simp]
theorem rectangularUnitSwitch_switch (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    rectangularUnitSwitch B A (rectangularUnitSwitch A B g hg)
      (rectangularUnitSwitch_val A B g hg) = g := by
  apply Units.ext
  rw [rectangularUnitSwitch_val]
  exact hg.symm

/-- The diagonal pair is an ordered product of four rectangular shears. -/
theorem diagonalPairUnit_rectangularUnitSwitch_inv_eq
    (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    diagonalPairUnit g ((rectangularUnitSwitch A B g hg)⁻¹) =
      rectangularUpperUnit A * rectangularLowerUnit B *
        rectangularUpperUnit (-(((g⁻¹ : GL X R) : Matrix X X R) * A)) *
        rectangularLowerUnit (-(B * (g : Matrix X X R))) := by
  let P : Matrix X X R := g
  let T : Matrix X X R := ((g⁻¹ : GL X R) : Matrix X X R)
  let S : Matrix Y Y R := 1 - B * T * A
  have hPT : P * T = 1 := by
    simpa only [P, T, Units.val_mul, Units.val_one] using
      congrArg (fun u : GL X R => (u : Matrix X X R)) (mul_inv_cancel g)
  have hTP : T * P = 1 := by
    simpa only [P, T, Units.val_mul, Units.val_one] using
      congrArg (fun u : GL X R => (u : Matrix X X R)) (inv_mul_cancel g)
  have hAP : A * B = P - 1 := by
    dsimp [P]
    rw [hg]
    simp
  have hPTA : P * (T * A) = A := by
    rw [← Matrix.mul_assoc, hPT, Matrix.one_mul]
  have hTAB : T * A * B = 1 - T := by
    rw [Matrix.mul_assoc, hAP, Matrix.mul_sub, hTP, Matrix.mul_one]
  have hSB : S * B = B * T := by
    simp only [S, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T A B, hTAB, Matrix.mul_sub, Matrix.mul_one]
    simp
  have hSBP : S * (B * P) = B := by
    rw [← Matrix.mul_assoc, hSB, Matrix.mul_assoc, hTP, Matrix.mul_one]
  have hfirst : ((rectangularUpperUnit A * rectangularLowerUnit B : GL (X ⊕ Y) R) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) = Matrix.fromBlocks P A B 1 := by
    rw [Units.val_mul, rectangularUpperUnit_val, rectangularLowerUnit_val,
      Matrix.fromBlocks_multiply]
    simp [P, ← hg]
  have hsecond : ((rectangularUpperUnit A * rectangularLowerUnit B *
      rectangularUpperUnit (-(T * A)) : GL (X ⊕ Y) R) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) = Matrix.fromBlocks P 0 B S := by
    rw [Units.val_mul, hfirst, rectangularUpperUnit_val, Matrix.fromBlocks_multiply]
    simp [hPTA, S, Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg, add_comm]
  apply Units.ext
  rw [diagonalPairUnit_val, rectangularUnitSwitch_inv_val]
  change Matrix.fromBlocks P 0 0 S = _
  rw [Units.val_mul, hsecond, rectangularLowerUnit_val, Matrix.fromBlocks_multiply]
  simp only [mul_one, Matrix.mul_neg, Matrix.zero_mul, neg_zero, add_zero,
    Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.fromBlocks_inj, and_true, true_and]
  change 0 = B + -(S * (B * P))
  rw [hSBP]
  exact (add_neg_cancel B).symm

/-- The diagonal pair of a unit and its inverse switched unit is elementary. -/
theorem diagonalPairUnit_rectangularUnitSwitch_inv_mem_elementarySubgroup
    (A : Matrix X Y R) (B : Matrix Y X R)
    (g : GL X R) (hg : (g : Matrix X X R) = 1 + A * B) :
    diagonalPairUnit g ((rectangularUnitSwitch A B g hg)⁻¹) ∈
      elementarySubgroup (X ⊕ Y) R := by
  rw [diagonalPairUnit_rectangularUnitSwitch_inv_eq A B g hg]
  exact (elementarySubgroup (X ⊕ Y) R).mul_mem
    ((elementarySubgroup (X ⊕ Y) R).mul_mem
      ((elementarySubgroup (X ⊕ Y) R).mul_mem
        (rectangularUpperUnit_mem_elementarySubgroup A)
        (rectangularLowerUnit_mem_elementarySubgroup B))
      (rectangularUpperUnit_mem_elementarySubgroup
        (-(((g⁻¹ : GL X R) : Matrix X X R) * A))))
    (rectangularLowerUnit_mem_elementarySubgroup (-(B * (g : Matrix X X R))))

/-- Switching a zero-product unit gives the identity on the other block. -/
@[simp]
theorem rectangularUnitSwitch_zeroProductUnit (A : Matrix X Y R) (B : Matrix Y X R)
    (hBA : B * A = 0) :
    rectangularUnitSwitch A B (zeroProductUnit A B hBA)
      (zeroProductUnit_val A B hBA) = 1 := by
  apply Units.ext
  simp [rectangularUnitSwitch_val, hBA]

/-- For zero-product blocks the switched diagonal pair is the published stabilization
commutator. -/
theorem diagonalPairUnit_zeroProductUnit_rectangularUnitSwitch_inv_eq
    (A : Matrix X Y R) (B : Matrix Y X R) (hBA : B * A = 0) :
    diagonalPairUnit (zeroProductUnit A B hBA)
      ((rectangularUnitSwitch A B (zeroProductUnit A B hBA)
        (zeroProductUnit_val A B hBA))⁻¹) =
      rectangularUpperUnit A * rectangularLowerUnit B *
        (rectangularUpperUnit A)⁻¹ * (rectangularLowerUnit B)⁻¹ := by
  rw [rectangularUnitSwitch_zeroProductUnit, inv_one, diagonalPairUnit_one_right]
  exact stabilize_zeroProductUnit_eq A B hBA

end Matrix.GeneralLinearGroup
