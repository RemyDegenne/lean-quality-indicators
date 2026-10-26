/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.CongruenceSubgroup
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotent matrices over nonunital rings

This file defines strictly positive powers and nilpotence without assuming a
multiplicative identity.  It relates that notion to ordinary nilpotence after
canonical inclusion into a unitization, and constructs the corresponding
element of the relative general linear group.

It also proves directly that a strictly upper triangular square matrix over an
arbitrary nonunital ring is nilpotent.  No commutativity is used.
-/

set_option warningAsError true

@[expose] public section

namespace NonUnital

universe u

variable {A : Type u}

/-- The product of `k + 1` copies of an element, defined without a
multiplicative identity. -/
def positivePow [Mul A] (x : A) : ℕ → A :=
  Nat.rec x (fun _ y => y * x)

/-- The zeroth index of the positive-power sequence is the product of one copy of `x`. -/
@[simp]
theorem positivePow_zero [Mul A] (x : A) : positivePow x 0 = x := rfl

/-- The next positive power is obtained by multiplying the preceding product by `x` on the right. -/
@[simp]
theorem positivePow_succ [Mul A] (x : A) (k : ℕ) :
    positivePow x (k + 1) = positivePow x k * x := rfl

/-- Nilpotence in a possibly nonunital multiplicative structure: some
strictly positive power is zero. -/
def IsNilpotent [SemigroupWithZero A] (x : A) : Prop :=
  ∃ k, positivePow x k = 0

end NonUnital

/-- If `r ^ k = 0`, package `1 + r` as a unit with its explicit finite
alternating geometric-series inverse. -/
def IsNilpotent.oneAddUnitOfPowEqZero {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) : Aˣ where
  val := 1 + r
  inv := ∑ i ∈ Finset.range k, (-r) ^ i
  val_inv := by
    have hneg : (-r : A) ^ k = 0 := by
      rw [neg_pow, hk, mul_zero]
    change (1 + r) * (∑ i ∈ Finset.range k, (-r) ^ i) = 1
    rw [show 1 + r = 1 - (-r) by abel, mul_neg_geom_sum, hneg, sub_zero]
  inv_val := by
    have hneg : (-r : A) ^ k = 0 := by
      rw [neg_pow, hk, mul_zero]
    change (∑ i ∈ Finset.range k, (-r) ^ i) * (1 + r) = 1
    rw [show 1 + r = 1 - (-r) by abel, geom_sum_mul_neg, hneg, sub_zero]

/-- The unit constructed from `r ^ k = 0` has underlying ring element `1 + r`. -/
@[simp]
theorem IsNilpotent.oneAddUnitOfPowEqZero_val {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) :
    (IsNilpotent.oneAddUnitOfPowEqZero r k hk : A) = 1 + r := rfl

/-- The stored inverse of the unit `1 + r` is the finite sum of `(-r) ^ i` for `i < k`. -/
@[simp]
theorem IsNilpotent.oneAddUnitOfPowEqZero_inv {A : Type*} [Ring A]
    (r : A) (k : ℕ) (hk : r ^ k = 0) :
    (IsNilpotent.oneAddUnitOfPowEqZero r k hk).inv =
      ∑ i ∈ Finset.range k, (-r) ^ i := rfl

namespace Matrix

universe u

variable {I : Type u} [NonUnitalRing I]
variable {n : ℕ}

/-- Literal strict upper triangularity: diagonal and below-diagonal entries
vanish. -/
def IsStrictlyUpperTriangular (x : Matrix (Fin n) (Fin n) I) : Prop :=
  ∀ i j, j.val ≤ i.val → x i j = 0

/-- After multiplying `k + 1` copies of a strictly upper triangular matrix,
possible nonzero entries lie at least `k + 1` places above the diagonal. -/
theorem positivePow_apply_eq_zero_of_isStrictlyUpperTriangular
    {x : Matrix (Fin n) (Fin n) I} (hx : x.IsStrictlyUpperTriangular) :
    ∀ (k : ℕ) (i j : Fin n),
      j.val < i.val + (k + 1) → NonUnital.positivePow x k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro i j hij
      exact hx i j (by omega)
  | succ k ih =>
      intro i j hij
      rw [NonUnital.positivePow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : l.val < i.val + (k + 1)
      · rw [ih i l hil, zero_mul]
      · have hjl : j.val ≤ l.val := by omega
        rw [hx l j hjl, mul_zero]

/-- A strictly upper triangular `n × n` matrix over a nonunital ring is
nilpotent.  The witness here is the deliberately uniform product of `n + 1`
copies, which also handles the empty matrix without a separate case. -/
theorem IsStrictlyUpperTriangular.isNilpotent
    {x : Matrix (Fin n) (Fin n) I} (hx : x.IsStrictlyUpperTriangular) :
    NonUnital.IsNilpotent x := by
  refine ⟨n, ?_⟩
  ext i j
  apply positivePow_apply_eq_zero_of_isStrictlyUpperTriangular hx
  omega

namespace GeneralLinearGroup

universe v

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- Entrywise inclusion of a matrix over a nonunital ring into its canonical
unitization. -/
def unitizationMatrix (x : Matrix n n I) : Matrix n n (Unitization ℤ I) :=
  x.map fun a ↦ (a : Unitization ℤ I)

omit [Fintype n] [DecidableEq n] in
/-- Entrywise inclusion into the unitization sends the zero matrix to zero. -/
@[simp]
theorem unitizationMatrix_zero :
    unitizationMatrix (0 : Matrix n n I) = 0 := by
  apply Matrix.ext
  intro i j
  apply Unitization.ext <;> simp [unitizationMatrix]

omit [DecidableEq n] in
/-- Entrywise inclusion into the unitization preserves multiplication of finite square matrices. -/
theorem unitizationMatrix_mul (x y : Matrix n n I) :
    unitizationMatrix (x * y) = unitizationMatrix x * unitizationMatrix y := by
  apply Matrix.ext
  intro i j
  apply Unitization.ext
  · change 0 = (Unitization.fstHom (R := ℤ) (A := I)).toRingHom
      (∑ k, (x i k : Unitization ℤ I) * (y k j : Unitization ℤ I))
    rw [map_sum]
    simp
  · change (∑ k, x i k * y k j) =
      (Unitization.sndHom ℤ ℤ I)
        (∑ k, (x i k : Unitization ℤ I) * (y k j : Unitization ℤ I))
    rw [map_sum]
    simp [Unitization.snd_mul]

/-- A product of `k + 1` nonunital matrix factors maps to the ordinary `(k + 1)`st power. -/
theorem unitizationMatrix_positivePow (x : Matrix n n I) (k : ℕ) :
    unitizationMatrix (NonUnital.positivePow x k) =
      unitizationMatrix x ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        unitizationMatrix (NonUnital.positivePow x (k + 1)) =
            unitizationMatrix (NonUnital.positivePow x k) *
              unitizationMatrix x := by
                rw [NonUnital.positivePow_succ, unitizationMatrix_mul]
        _ = unitizationMatrix x ^ (k + 1) * unitizationMatrix x := by
          rw [ih]
        _ = unitizationMatrix x ^ (k + 1 + 1) :=
          (pow_succ (unitizationMatrix x) (k + 1)).symm

/-- Nonunital nilpotence becomes ordinary nilpotence after entrywise
inclusion into the canonical unitization. -/
theorem isNilpotent_unitizationMatrix (x : Matrix n n I)
    (hx : NonUnital.IsNilpotent x) : IsNilpotent (unitizationMatrix x) := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨k + 1, ?_⟩
  rw [← unitizationMatrix_positivePow, hk, unitizationMatrix_zero]

/-- The augmentation from the general linear group over a nonunital ring's
unitization to the general linear group over `ℤ`. -/
def nonUnitalAugmentation : GL n (Unitization ℤ I) →* GL n ℤ :=
  mapRingHom (Unitization.fstHom (R := ℤ) (A := I)).toRingHom

/-- The general linear group of an arbitrary nonunital ring, defined as the
kernel of the augmentation on its canonical unitization. -/
def nonUnitalGeneralLinearGroup : Subgroup (GL n (Unitization ℤ I)) :=
  MonoidHom.ker (nonUnitalAugmentation (n := n) (I := I))

/-- A matrix whose entrywise image in the canonical unitization has a
vanishing power determines an element of the nonunital general linear group. -/
def nilpotentMatrixElement
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    nonUnitalGeneralLinearGroup (n := n) (I := I) := by
  refine ⟨IsNilpotent.oneAddUnitOfPowEqZero (unitizationMatrix x) k hk, ?_⟩
  apply Units.ext
  ext i j
  by_cases h : i = j <;>
    simp [nonUnitalAugmentation, unitizationMatrix, h]

/-- The relative general-linear-group element from a vanishing power has matrix `1 + x`
after entrywise inclusion into the unitization. -/
@[simp]
theorem nilpotentMatrixElement_val
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    ((nilpotentMatrixElement x k hk).1 : Matrix n n (Unitization ℤ I)) =
      1 + unitizationMatrix x := rfl

/-- The stored inverse of the relative element is the finite alternating geometric series
in the unitized matrix, with length the supplied nilpotence exponent. -/
@[simp]
theorem nilpotentMatrixElement_inv
    (x : Matrix n n I) (k : ℕ) (hk : unitizationMatrix x ^ k = 0) :
    (nilpotentMatrixElement x k hk).1.inv =
      ∑ i ∈ Finset.range k, (-unitizationMatrix x) ^ i := rfl

/-- A nilpotent matrix over a nonunital ring canonically determines the
relative general-linear-group element represented by `1 + x`. -/
noncomputable def nonUnitalGeneralLinearGroupOfIsNilpotent
    (x : Matrix n n I) (hx : NonUnital.IsNilpotent x) :
    nonUnitalGeneralLinearGroup (n := n) (I := I) :=
  nilpotentMatrixElement x (isNilpotent_unitizationMatrix x hx).choose
    (isNilpotent_unitizationMatrix x hx).choose_spec

/-- Choosing a nilpotence exponent does not change the underlying matrix `1 + x`
of the resulting relative general-linear-group element. -/
@[simp]
theorem nonUnitalGeneralLinearGroupOfIsNilpotent_val
    (x : Matrix n n I) (hx : NonUnital.IsNilpotent x) :
    ((nonUnitalGeneralLinearGroupOfIsNilpotent x hx).1 :
      Matrix n n (Unitization ℤ I)) = 1 + unitizationMatrix x :=
  nilpotentMatrixElement_val _ _ _

end GeneralLinearGroup

end Matrix
