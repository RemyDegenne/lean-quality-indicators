/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.UnitPivotDiagonalization

/-! Schur reduction at a unit northwest block over an arbitrary ring. -/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} {R : Type uR}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Ring R]

/-- The block unit with specified northwest pivot, off-diagonal blocks and unit
Schur residual, assembled using the existing lower and triangular units. -/
def schurBlockUnit (A : GL X R) (B : Matrix X Y R)
    (C : Matrix Y X R) (S : GL Y R) : GL (X ⊕ Y) R :=
  rectangularLowerUnit (C * ((A⁻¹ : GL X R) : Matrix X X R)) *
    triangularUnit A B S

/-- The elementary lower and upper shears give the ordered LDU factorization. -/
theorem schurBlockUnit_eq_lower_mul_diagonal_mul_upper
    (A : GL X R) (B : Matrix X Y R) (C : Matrix Y X R) (S : GL Y R) :
    schurBlockUnit A B C S =
      rectangularLowerUnit (C * ((A⁻¹ : GL X R) : Matrix X X R)) *
        diagonalPairUnit A S *
          rectangularUpperUnit (((A⁻¹ : GL X R) : Matrix X X R) * B) := by
  rw [schurBlockUnit, triangularUnit_eq_diagonal_mul_upper, mul_assoc]

@[simp]
theorem schurBlockUnit_val
    (A : GL X R) (B : Matrix X Y R) (C : Matrix Y X R) (S : GL Y R) :
    (schurBlockUnit A B C S : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks (A : Matrix X X R) B C
        (C * ((A⁻¹ : GL X R) : Matrix X X R) * B + (S : Matrix Y Y R)) := by
  simp only [schurBlockUnit, Units.val_mul, rectangularLowerUnit_val, triangularUnit_val,
    Matrix.fromBlocks_multiply, one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    Matrix.fromBlocks_inj, true_and, and_true]
  rw [Matrix.mul_assoc, ← Units.val_mul]
  simp

/-- Reading the southeast corner and subtracting the ordered cross term returns
the specified Schur residual. -/
theorem schurBlockUnit_schur
    (A : GL X R) (B : Matrix X Y R) (C : Matrix Y X R) (S : GL Y R) :
    (schurBlockUnit A B C S : Matrix (X ⊕ Y) (X ⊕ Y) R).toBlocks₂₂ -
        (schurBlockUnit A B C S : Matrix (X ⊕ Y) (X ⊕ Y) R).toBlocks₂₁ *
          ((A⁻¹ : GL X R) : Matrix X X R) *
        (schurBlockUnit A B C S : Matrix (X ⊕ Y) (X ⊕ Y) R).toBlocks₁₂ =
      (S : Matrix Y Y R) := by
  simp [schurBlockUnit_val]

/-- The inverse of a Schur block unit, with the noncommutative factors in order. -/
@[simp]
theorem schurBlockUnit_inv_val
    (A : GL X R) (B : Matrix X Y R) (C : Matrix Y X R) (S : GL Y R) :
    (((schurBlockUnit A B C S)⁻¹ : GL (X ⊕ Y) R) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks
        (((A⁻¹ : GL X R) : Matrix X X R) +
          ((A⁻¹ : GL X R) : Matrix X X R) * B *
            ((S⁻¹ : GL Y R) : Matrix Y Y R) * C *
              ((A⁻¹ : GL X R) : Matrix X X R))
        (-(((A⁻¹ : GL X R) : Matrix X X R) * B *
          ((S⁻¹ : GL Y R) : Matrix Y Y R)))
        (-(((S⁻¹ : GL Y R) : Matrix Y Y R) * C *
          ((A⁻¹ : GL X R) : Matrix X X R)))
        ((S⁻¹ : GL Y R) : Matrix Y Y R) := by
  have hInv : (schurBlockUnit A B C S)⁻¹ =
      (triangularUnit A B S)⁻¹ *
        (rectangularLowerUnit (C * ((A⁻¹ : GL X R) : Matrix X X R)))⁻¹ := by
    exact _root_.mul_inv_rev _ _
  rw [hInv, Units.val_mul, triangularUnit_inv_val,
    rectangularLowerUnit_inv, rectangularLowerUnit_val, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

/-- Zero off-diagonal blocks recover the existing diagonal block unit. -/
@[simp]
theorem schurBlockUnit_zero_zero (A : GL X R) (S : GL Y R) :
    schurBlockUnit A (0 : Matrix X Y R) (0 : Matrix Y X R) S =
      diagonalPairUnit A S := by
  apply Units.ext
  simp [schurBlockUnit_val, diagonalPairUnit_val]

/-- With an empty trailing block, the Schur construction is stabilization. -/
theorem schurBlockUnit_empty_right (A : GL X R) :
    schurBlockUnit A (0 : Matrix X (Fin 0) R) (0 : Matrix (Fin 0) X R)
        (1 : GL (Fin 0) R) = stabilize A := by
  simp [schurBlockUnit_zero_zero, diagonalPairUnit_one_right]

/-- With an empty leading block, the Schur construction is trailing
stabilization, reindexed into the original block order. -/
theorem schurBlockUnit_empty_left (S : GL Y R) :
    schurBlockUnit (1 : GL (Fin 0) R) (0 : Matrix (Fin 0) Y R)
      (0 : Matrix Y (Fin 0) R) S =
        reindexEquiv R (Equiv.sumComm Y (Fin 0)) (stabilize (Y := Fin 0) S) := by
  simp [schurBlockUnit_zero_zero, diagonalPairUnit_one_left]

/-- A group homomorphism killing elementary units reads only the diagonal pair;
no normality or commutativity of the target is assumed. -/
theorem map_schurBlockUnit_eq_diagonalPairUnit
    {G : Type uG} [Group G] (f : GL (X ⊕ Y) R →* G)
    (hf : elementarySubgroup (X ⊕ Y) R ≤ f.ker)
    (A : GL X R) (B : Matrix X Y R) (C : Matrix Y X R) (S : GL Y R) :
    f (schurBlockUnit A B C S) = f (diagonalPairUnit A S) := by
  rw [schurBlockUnit, map_mul, map_triangularUnit_eq_diagonalPairUnit f hf]
  have hmem := hf (rectangularLowerUnit_mem_elementarySubgroup
    (C * ((A⁻¹ : GL X R) : Matrix X X R)))
  simp only [MonoidHom.mem_ker] at hmem
  rw [hmem, one_mul]

/-- A supplied block unit has the same image as its pivot and residual. -/
theorem map_unit_eq_diagonalPairUnit_of_fromBlocks
    {G : Type uG} [Group G] (f : GL (X ⊕ Y) R →* G)
    (hf : elementarySubgroup (X ⊕ Y) R ≤ f.ker)
    (M : GL (X ⊕ Y) R) (A : GL X R) (B : Matrix X Y R)
    (C : Matrix Y X R) (D : Matrix Y Y R)
    (hM : (M : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks (A : Matrix X X R) B C D)
    (S : GL Y R)
    (hS : (S : Matrix Y Y R) =
      D - C * ((A⁻¹ : GL X R) : Matrix X X R) * B) :
    f M = f (diagonalPairUnit A S) := by
  have hD : D = C * ((A⁻¹ : GL X R) : Matrix X X R) * B +
      (S : Matrix Y Y R) := by
    rw [hS]
    simp
  have heq : M = schurBlockUnit A B C S := by
    apply Units.ext
    simpa only [schurBlockUnit_val] using hM.trans (by rw [hD])
  rw [heq]
  exact map_schurBlockUnit_eq_diagonalPairUnit f hf A B C S

end Matrix.GeneralLinearGroup

namespace Matrix

universe uX uY uR

variable {X : Type uX} {Y : Type uY} {R : Type uR}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Ring R]

/-- With a known unit northwest pivot, a block matrix is a unit precisely when
its ordered Schur residual is a unit. -/
theorem isUnit_fromBlocks_iff_of_invertible₁₁_ring
    {A : Matrix X X R} {B : Matrix X Y R}
    {C : Matrix Y X R} {D : Matrix Y Y R} [Invertible A] :
    IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (D - C * ⅟A * B) := by
  obtain ⟨L, Q, hreduce⟩ := fromBlocks_elementary_reduce A B C D
  have hiff : IsUnit (Matrix.fromBlocks A B C D) ↔
      IsUnit (Matrix.fromBlocks A 0 0 (D - C * ⅟A * B)) := by
    rw [← hreduce]
    change IsUnit (Matrix.fromBlocks A B C D) ↔
      IsUnit (((L : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) *
        Matrix.fromBlocks A B C D *
        ((Q : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R))
    simp
  rw [hiff]
  constructor
  · intro hdiag
    obtain ⟨N, hright, hleft⟩ := isUnit_iff_exists.mp hdiag
    have hright' : (D - C * ⅟A * B) * N.toBlocks₂₂ = 1 := by
      rw [← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply] at hright
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
        ← Matrix.fromBlocks_one] using congrArg Matrix.toBlocks₂₂ hright
    have hleft' : N.toBlocks₂₂ * (D - C * ⅟A * B) = 1 := by
      rw [← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply] at hleft
      simpa only [Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_zero, zero_add,
        ← Matrix.fromBlocks_one] using congrArg Matrix.toBlocks₂₂ hleft
    exact isUnit_iff_exists.mpr ⟨N.toBlocks₂₂, hright', hleft'⟩
  · rintro ⟨S, hS⟩
    rw [← hS]
    refine ⟨GeneralLinearGroup.diagonalPairUnit (unitOfInvertible A) S, ?_⟩
    exact GeneralLinearGroup.diagonalPairUnit_val (unitOfInvertible A) S

end Matrix

namespace Matrix.GeneralLinearGroup

universe uX uY uR

variable {X : Type uX} {Y : Type uY} {R : Type uR}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [CommRing R]

/-- Under commutativity the Ring criterion specializes to Mathlib's northwest
pivot criterion, with each direction supplied by one of the two versions. -/
theorem isUnit_fromBlocks_iff_of_invertible₁₁_ring_comm
    {A : Matrix X X R} {B : Matrix X Y R}
    {C : Matrix Y X R} {D : Matrix Y Y R} [Invertible A] :
    IsUnit (Matrix.fromBlocks A B C D) ↔ IsUnit (D - C * ⅟A * B) :=
  ⟨Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp,
    Matrix.isUnit_fromBlocks_iff_of_invertible₁₁_ring.mpr⟩

end Matrix.GeneralLinearGroup

namespace Matrix.GeneralLinearGroup

universe uX uY uR

variable {X : Type uX} {Y : Type uY} {R : Type uR}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Ring R]

/-- The inverse of the Schur unit agrees with `invOf` on its block matrix value
for any choice of an invertibility instance on that matrix. -/
theorem schurBlockUnit_inv_eq_invOf_fromBlocks₁₁
    (A : GL X R) (B : Matrix X Y R) (C : Matrix Y X R) (S : GL Y R)
    [Invertible (Matrix.fromBlocks (A : Matrix X X R) B C
      (C * ((A⁻¹ : GL X R) : Matrix X X R) * B + (S : Matrix Y Y R)))] :
    (((schurBlockUnit A B C S)⁻¹ : GL (X ⊕ Y) R) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) =
      ⅟(Matrix.fromBlocks (A : Matrix X X R) B C
        (C * ((A⁻¹ : GL X R) : Matrix X X R) * B + (S : Matrix Y Y R))) := by
  symm
  apply invOf_eq_right_inv
  rw [← schurBlockUnit_val]
  exact Units.val_inv (schurBlockUnit A B C S)

end Matrix.GeneralLinearGroup
