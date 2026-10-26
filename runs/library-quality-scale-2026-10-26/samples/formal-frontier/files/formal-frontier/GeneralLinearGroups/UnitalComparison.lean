/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.NonUnitalNilpotent
import Mathlib.Tactic.NoncommRing

/-!
# Unital rings viewed through unitization

For a unital algebra, its unitization is canonically the product of the scalar
ring and the original algebra.  At the level of finite general linear groups,
this identifies the augmentation-kernel definition for a nonunital ring with
the ordinary general linear group whenever the coefficient ring has a unit.

No commutativity is assumed for the coefficient algebra, and the matrix index
type may be empty.
-/

set_option warningAsError true

@[expose] public section

namespace Unitization

universe u v

variable (R : Type u) (A : Type v)
variable [CommRing R] [Ring A] [Algebra R A]

/-- The canonical ring equivalence from the unitization of a unital algebra to
the product of its scalar ring and the algebra itself.  It sends `(r, a)` to
`(r, algebraMap R A r + a)`. -/
def ringEquivProd : Unitization R A ≃+* R × A where
  toFun x := (x.fst, algebraMap R A x.fst + x.snd)
  invFun x := Unitization.mk (x.1, x.2 - algebraMap R A x.1)
  left_inv x := by
    apply Unitization.ext
    · rfl
    · simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change algebraMap R A (x.fst + y.fst) + (x.snd + y.snd) =
        (algebraMap R A x.fst + x.snd) +
          (algebraMap R A y.fst + y.snd)
      rw [map_add]
      abel
  map_mul' x y := by
    apply Prod.ext
    · exact Unitization.fst_mul x y
    · change algebraMap R A (x.fst * y.fst) +
          (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) =
        (algebraMap R A x.fst + x.snd) *
          (algebraMap R A y.fst + y.snd)
      simp only [map_mul, Algebra.smul_def]
      rw [Algebra.commutes y.fst x.snd]
      noncomm_ring

/-- The product coordinates retain the scalar part and add its algebra image to the algebra part. -/
@[simp]
theorem ringEquivProd_apply (x : Unitization R A) :
    ringEquivProd R A x =
      (x.fst, algebraMap R A x.fst + x.snd) := rfl

/-- Recover the unitized coefficient by subtracting the scalar's algebra image from the second
product coordinate. -/
@[simp]
theorem ringEquivProd_symm_apply (x : R × A) :
    (ringEquivProd R A).symm x =
      Unitization.mk (x.1, x.2 - algebraMap R A x.1) := rfl

end Unitization

namespace Matrix.GeneralLinearGroup

universe u v w

variable (R : Type u) (A : Type v)
variable [CommRing R] [Ring A] [Algebra R A]
variable {n : Type w} [Fintype n] [DecidableEq n]

/-- Matrices over a product ring are canonically a product of matrix rings. -/
def matrixRingEquivProd :
    Matrix n n (R × A) ≃+* Matrix n n R × Matrix n n A where
  toFun x := ((RingHom.fst R A).mapMatrix x,
    (RingHom.snd R A).mapMatrix x)
  invFun x i j := (x.1 i j, x.2 i j)
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by
    apply Prod.ext
    · exact (RingHom.fst R A).mapMatrix.map_add x y
    · exact (RingHom.snd R A).mapMatrix.map_add x y
  map_mul' x y := by
    apply Prod.ext
    · exact (RingHom.fst R A).mapMatrix.map_mul x y
    · exact (RingHom.snd R A).mapMatrix.map_mul x y

/-- The finite general linear group over a unital algebra's unitization is the
product of the general linear groups over the scalar ring and the algebra. -/
def unitizationGeneralLinearEquivProd :
    GL n (Unitization R A) ≃* GL n R × GL n A :=
  (Units.mapEquiv (Unitization.ringEquivProd R A).mapMatrix.toMulEquiv).trans
    ((Units.mapEquiv (matrixRingEquivProd R A).toMulEquiv).trans
      MulEquiv.prodUnits)

/-- The scalar factor of the product equivalence is the entrywise augmentation homomorphism. -/
@[simp]
theorem unitizationGeneralLinearEquivProd_fst
    (g : GL n (Unitization R A)) :
    (unitizationGeneralLinearEquivProd R A g).1 =
      mapRingHom (Unitization.fstHom (R := R) (A := A)).toRingHom g := by
  apply Units.ext
  ext i j
  simp [unitizationGeneralLinearEquivProd, matrixRingEquivProd]
  rfl

/-- For a unital ring, the augmentation-kernel definition of its finite
general linear group agrees canonically with the ordinary definition. -/
def nonUnitalGeneralLinearGroupEquiv (I : Type u) [Ring I] :
    nonUnitalGeneralLinearGroup (n := n) (I := I) ≃* GL n I where
  toFun g := (unitizationGeneralLinearEquivProd ℤ I g.1).2
  invFun g := by
    refine ⟨(unitizationGeneralLinearEquivProd ℤ I).symm (1, g), ?_⟩
    change nonUnitalAugmentation
      ((unitizationGeneralLinearEquivProd ℤ I).symm (1, g)) = 1
    unfold nonUnitalAugmentation
    rw [← unitizationGeneralLinearEquivProd_fst]
    simp
  left_inv g := by
    apply Subtype.ext
    apply (unitizationGeneralLinearEquivProd ℤ I).injective
    change unitizationGeneralLinearEquivProd ℤ I
        ((unitizationGeneralLinearEquivProd ℤ I).symm
          (1, (unitizationGeneralLinearEquivProd ℤ I g.1).2)) =
      unitizationGeneralLinearEquivProd ℤ I g.1
    calc
      _ = (1, (unitizationGeneralLinearEquivProd ℤ I g.1).2) :=
        (unitizationGeneralLinearEquivProd ℤ I).apply_symm_apply _
      _ = unitizationGeneralLinearEquivProd ℤ I g.1 := by
        apply Prod.ext
        · simpa [nonUnitalGeneralLinearGroup,
            nonUnitalAugmentation] using g.2.symm
        · rfl
  right_inv g := by
    change (unitizationGeneralLinearEquivProd ℤ I
      ((unitizationGeneralLinearEquivProd ℤ I).symm (1, g))).2 = g
    simp
  map_mul' x y := by
    exact congrArg Prod.snd
      ((unitizationGeneralLinearEquivProd ℤ I).map_mul x.1 y.1)

/-- For a unital coefficient ring, the relative-to-ordinary group equivalence takes the
second component of the unitization product equivalence. -/
@[simp]
theorem nonUnitalGeneralLinearGroupEquiv_apply
    (I : Type u) [Ring I]
    (g : nonUnitalGeneralLinearGroup (n := n) (I := I)) :
    nonUnitalGeneralLinearGroupEquiv I g =
      (unitizationGeneralLinearEquivProd ℤ I g.1).2 := rfl

/-- The inverse relative-to-ordinary equivalence lifts an ordinary unit with
scalar component one. -/
@[simp]
theorem nonUnitalGeneralLinearGroupEquiv_symm_val
    (I : Type u) [Ring I] (g : GL n I) :
    ((nonUnitalGeneralLinearGroupEquiv I).symm g).1 =
      (unitizationGeneralLinearEquivProd ℤ I).symm (1, g) := rfl

end Matrix.GeneralLinearGroup
