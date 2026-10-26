/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RightRowCompletion
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Square construction for right-coefficient rows

A chosen section column and coordinates on the right-linear coefficient kernel
give an element of the general linear group with the original row and the
chosen inverse column. For a genuinely free kernel, invariant basis number
identifies the number of chosen kernel coordinates with the row length minus
one. Conversely, a square completion supplies free kernel coordinates without
any invariant-basis-number assumption.

The square criterion is stated in `StableRange.SquareRightRowCompletionCriterion`.
These constructions do not resolve the dimension-unspecified interpretation
of unimodular-row completion outside invariant-basis-number rings.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  I.1.2.1 (free-kernel/basis-extension idea).
* Mathlib, `LinearAlgebra.Matrix.InvariantBasisNumber` and
  `LinearAlgebra.Matrix.GeneralLinearGroup.Defs` (coordinate cardinality and
  matrix units).
* `StableRange.RightRowCompletion` (right-linear splitting and rectangular
  matrix actions).
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace LinearEquiv

universe u

/-- A free right coefficient kernel of a right-unimodular successor-length row
has coordinates indexed by the remaining entries, over an IBN ring. The
coordinate count follows from Mathlib's two-sided rectangular-matrix theorem. -/
noncomputable def rightCoefficientFreeKernelCoordinatesOfIBN (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a : Fin (m + 1) → R)
    (ha : Bass.IsRightUnimodular a)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) :
    LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R) := by
  obtain ⟨k, e⟩ := rightCoefficientFreeKernelCoordinates R a ha hfree
  let b := Classical.choose ha
  have hb : dotProductBilin R Rᵐᵒᵖ a b = 1 := Classical.choose_spec ha
  have hk : k = m := by
    have hcard := Matrix.square_of_invertible
      (Matrix.rightRowCompletion R a b hb e)
      (Matrix.rightRowCompletionInv R a b hb e)
      (Matrix.rightRowCompletion_mul_inv R a b hb e)
      (Matrix.rightRowCompletion_inv_mul R a b hb e)
    have hlength : k + 1 = m + 1 := by
      simpa only [Fintype.card_fin] using hcard
    exact Nat.add_right_cancel hlength
  subst k
  exact e

end LinearEquiv

namespace Matrix

universe u

/-- The square unit built from a specified right-inverse column and already
matching coordinates on the right coefficient kernel. This construction needs
no invariant-basis-number assumption. -/
noncomputable def rightRowCompletionGL (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    GeneralLinearGroup (Fin (m + 1)) R :=
  ⟨rightRowCompletion R a b hb e, rightRowCompletionInv R a b hb e,
    rightRowCompletion_mul_inv R a b hb e,
    rightRowCompletion_inv_mul R a b hb e⟩

@[simp]
theorem rightRowCompletionGL_val (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (rightRowCompletionGL R a b hb e : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      rightRowCompletion R a b hb e := rfl

@[simp]
theorem rightRowCompletionGL_inv_val (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    ((rightRowCompletionGL R a b hb e)⁻¹).val =
      rightRowCompletionInv R a b hb e := rfl

/-- The first row of the square completion is the original coefficient row. -/
@[simp]
theorem rightRowCompletionGL_zero (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (rightRowCompletionGL R a b hb e : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 = a := by
  rw [rightRowCompletionGL_val, rightRowCompletion_zero]

/-- The first column of the inverse is the supplied right-unimodularity witness. -/
theorem rightRowCompletionGL_inv_zero (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R)) :
    (fun i ↦ ((rightRowCompletionGL R a b hb e)⁻¹).val i 0) = b := by
  rw [rightRowCompletionGL_inv_val]
  exact rightRowCompletionInv_zero R a b hb e

@[simp]
theorem rightRowCompletionGL_inv_apply_zero (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (i : Fin (m + 1)) :
    ((rightRowCompletionGL R a b hb e)⁻¹).val i 0 = b i :=
  congrFun (rightRowCompletionGL_inv_zero R a b hb e) i

/-- The forward action records the coefficient and chosen kernel coordinates. -/
theorem rightRowCompletionGL_mulVec (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (x : Fin (m + 1) → R) :
    (rightRowCompletionGL R a b hb e : Matrix (Fin (m + 1)) (Fin (m + 1)) R) *ᵥ x =
      LinearEquiv.rightCoefficientRowCoordinates R a b hb e x := by
  rw [rightRowCompletionGL_val, rightRowCompletion_mulVec]

/-- The inverse action reconstructs the input using the specified column,
with multiplication on the left of its original coefficient. -/
theorem rightRowCompletionGL_inv_mulVec (R : Type u) [Ring R]
    {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (e : LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a) ≃ₗ[Rᵐᵒᵖ] (Fin m → R))
    (y : Fin (m + 1) → R) (i : Fin (m + 1)) :
    (((rightRowCompletionGL R a b hb e)⁻¹).val *ᵥ y) i =
        b i * y 0 + (e.symm (Fin.tail y)).1 i := by
  rw [rightRowCompletionGL_inv_val, rightRowCompletionInv_mulVec]
  exact LinearEquiv.rightCoefficientRowCoordinates_symm_apply R a b hb e y i

/-- Choose a GL completion from genuine freeness of the kernel. IBN is used
only to identify the cardinality of the free kernel basis with the remaining
row coordinates. -/
noncomputable def rightRowCompletionGLOfFree (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) :
    GeneralLinearGroup (Fin (m + 1)) R :=
  rightRowCompletionGL R a b hb
    (LinearEquiv.rightCoefficientFreeKernelCoordinatesOfIBN R a ⟨b, hb⟩ hfree)

/-- The chosen GL completion retains its original row. -/
@[simp]
theorem rightRowCompletionGLOfFree_zero (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) :
    (rightRowCompletionGLOfFree R a b hb hfree :
      Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 = a :=
  rightRowCompletionGL_zero R a b hb _

/-- The original section column is the inverse column of the chosen unit. -/
theorem rightRowCompletionGLOfFree_inv_zero (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a))) :
    (fun i ↦ ((rightRowCompletionGLOfFree R a b hb hfree)⁻¹).val i 0) = b :=
  rightRowCompletionGL_inv_zero R a b hb _

@[simp]
theorem rightRowCompletionGLOfFree_inv_apply_zero (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)))
    (i : Fin (m + 1)) :
    ((rightRowCompletionGLOfFree R a b hb hfree)⁻¹).val i 0 = b i :=
  congrFun (rightRowCompletionGLOfFree_inv_zero R a b hb hfree) i

/-- The completion chosen from freeness acts by its original coefficient
functional and its chosen finite kernel coordinates. -/
theorem rightRowCompletionGLOfFree_mulVec (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)))
    (x : Fin (m + 1) → R) :
    (rightRowCompletionGLOfFree R a b hb hfree :
      Matrix (Fin (m + 1)) (Fin (m + 1)) R) *ᵥ x =
        LinearEquiv.rightCoefficientRowCoordinates R a b hb
          (LinearEquiv.rightCoefficientFreeKernelCoordinatesOfIBN R a
            ⟨b, hb⟩ hfree) x :=
  rightRowCompletionGL_mulVec R a b hb _ x

/-- Inverse action of the completion chosen from freeness, with the supplied
section column on the left of the scalar coefficient. -/
theorem rightRowCompletionGLOfFree_inv_mulVec (R : Type u)
    [Ring R] [InvariantBasisNumber R] {m : ℕ} (a b : Fin (m + 1) → R)
    (hb : dotProductBilin R Rᵐᵒᵖ a b = 1)
    (hfree : Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)))
    (y : Fin (m + 1) → R) (i : Fin (m + 1)) :
    (((rightRowCompletionGLOfFree R a b hb hfree)⁻¹).val *ᵥ y) i =
      b i * y 0 +
        ((LinearEquiv.rightCoefficientFreeKernelCoordinatesOfIBN R a
          ⟨b, hb⟩ hfree).symm (Fin.tail y)).1 i :=
  rightRowCompletionGL_inv_mulVec R a b hb _ y i

/-- A square GL completion gives kernel freeness over any ring, without IBN. -/
theorem free_rightCoefficientKernel_of_gl (R : Type u) [Ring R]
    {m : ℕ} (a : Fin (m + 1) → R)
    (g : GeneralLinearGroup (Fin (m + 1)) R)
    (hrow : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) 0 = a) :
    Module.Free Rᵐᵒᵖ (LinearMap.ker (dotProductBilin R Rᵐᵒᵖ a)) := by
  have : Module.Free Rᵐᵒᵖ R :=
    Module.Free.of_equiv (MulOpposite.opLinearEquiv Rᵐᵒᵖ (M := R)).symm
  exact Module.Free.of_equiv
    (LinearEquiv.rightCoefficientKernelEquivOfMatrixInverse R a
      g.val g.inv hrow g.val_inv g.inv_val).symm

end Matrix
