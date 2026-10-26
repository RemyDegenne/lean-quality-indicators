/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RowKernel
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Explicit completion of a two-element coefficient row

A specified Bézout witness determines a matrix in `SL(2, R)` whose first
row is the original coefficient row. Its action identifies the kernel of
that row with `R`. Applying this identification to the first projection of
an equivalence `(Fin 2 → R) ≃ₗ[R] (R × P)` identifies `P` with `R`.

The construction uses the supplied witness, rather than choosing one from
`IsCoprime.exists_SL2_row`. The existing coefficient map and generic kernel
transport from `StableRange.RowKernel` retain the original projection.

## Implementation notes

The source works with right modules over a nonzero ring. Here the explicit
length-two matrix is stated for commutative rings and left linear maps;
the zero ring is included. No invariant-basis or stable-range condition is
used. No rectangular completion or noncommutative assertion is made.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, I.1.2.1.
* Mathlib, `Matrix.SpecialLinearGroup` (Bézout completion and inverse) and
  `Mathlib.LinearAlgebra.Matrix.ToLin` (matrix action).
* Formal Frontier, `StableRange.RowKernel` (coefficient maps and kernel transport).
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

/-- A determinant-one completion of a two-element row using its specified
Bézout coefficients. Unlike the existential `IsCoprime.exists_SL2_row`, this
retains the witness and hence determines the other row and inverse. -/
def coefficientRowCompletionTwo (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    SpecialLinearGroup (Fin 2) R :=
  ⟨!![a 0, a 1; -b 1, b 0], by
    rw [Matrix.det_fin_two_of]
    calc
      a 0 * b 0 - a 1 * -b 1 = a 0 * b 0 + a 1 * b 1 := by ring
      _ = 1 := h⟩

/-- The specified row is exactly the first row of the completed matrix. -/
@[simp]
theorem coefficientRowCompletionTwo_row_zero (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (coefficientRowCompletionTwo R a b h : Matrix (Fin 2) (Fin 2) R) 0 = a := by
  funext i
  fin_cases i <;> rfl

/-- The second row of the completion is determined by the specified Bézout witness. -/
@[simp]
theorem coefficientRowCompletionTwo_row_one (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (coefficientRowCompletionTwo R a b h : Matrix (Fin 2) (Fin 2) R) 1 = ![-b 1, b 0] := by
  funext i
  fin_cases i <;> rfl

/-- The inverse rows are `(b 0, -a 1)` and `(b 1, a 0)`. -/
theorem coefficientRowCompletionTwo_inv (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (↑((coefficientRowCompletionTwo R a b h)⁻¹) : Matrix (Fin 2) (Fin 2) R) =
      !![b 0, -a 1; b 1, a 0] := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coefficientRowCompletionTwo]

/-- Multiplication by the specified completion followed by its inverse. -/
theorem coefficientRowCompletionTwo_mul_inv (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (coefficientRowCompletionTwo R a b h : Matrix (Fin 2) (Fin 2) R) *
      (↑((coefficientRowCompletionTwo R a b h)⁻¹) : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp only [← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one]

/-- Multiplication by the inverse followed by the specified completion. -/
theorem coefficientRowCompletionTwo_inv_mul (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (↑((coefficientRowCompletionTwo R a b h)⁻¹) : Matrix (Fin 2) (Fin 2) R) *
      (coefficientRowCompletionTwo R a b h : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp only [← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one]

end Matrix

namespace LinearEquiv

universe u

/-- The linear action of the explicit length-two completion. -/
def coefficientRowCompletionTwo (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) :=
  (Matrix.coefficientRowCompletionTwo R a b h).toLin'

/-- The first output coordinate is the original coefficient functional. -/
@[simp]
theorem coefficientRowCompletionTwo_apply_zero (R : Type u) [CommRing R]
    (a b x : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    coefficientRowCompletionTwo R a b h x 0 =
      Bass.coefficientRowScalarMap R 2 a x := by
  change (Matrix.SpecialLinearGroup.toLin' (Matrix.coefficientRowCompletionTwo R a b h) x) 0 = _
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    Bass.coefficientRowScalarMap_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The second output coordinate of the completion. -/
@[simp]
theorem coefficientRowCompletionTwo_apply_one (R : Type u) [CommRing R]
    (a b x : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    coefficientRowCompletionTwo R a b h x 1 = -b 1 * x 0 + b 0 * x 1 := by
  change (Matrix.SpecialLinearGroup.toLin' (Matrix.coefficientRowCompletionTwo R a b h) x) 1 = _
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The inverse action at the first coordinate. -/
@[simp]
theorem coefficientRowCompletionTwo_symm_apply_zero (R : Type u) [CommRing R]
    (a b y : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (coefficientRowCompletionTwo R a b h).symm y 0 = b 0 * y 0 - a 1 * y 1 := by
  change ((Matrix.coefficientRowCompletionTwo R a b h).toLin').symm y 0 = _
  rw [Matrix.SpecialLinearGroup.toLin'_symm_apply, Matrix.toLin'_apply,
    Matrix.coefficientRowCompletionTwo_inv]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

/-- The inverse action at the second coordinate. -/
@[simp]
theorem coefficientRowCompletionTwo_symm_apply_one (R : Type u) [CommRing R]
    (a b y : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (coefficientRowCompletionTwo R a b h).symm y 1 = b 1 * y 0 + a 0 * y 1 := by
  change ((Matrix.coefficientRowCompletionTwo R a b h).toLin').symm y 1 = _
  rw [Matrix.SpecialLinearGroup.toLin'_symm_apply, Matrix.toLin'_apply,
    Matrix.coefficientRowCompletionTwo_inv]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end LinearEquiv

namespace Bass

universe u

/-- A two-element Bézout witness supplies Mathlib's `IsCoprime` predicate. -/
theorem isCoprime_of_coefficientRowTwo (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    IsCoprime (a 0) (a 1) :=
  ⟨b 0, b 1, by calc
    b 0 * a 0 + b 1 * a 1 = a 0 * b 0 + a 1 * b 1 := by ring
    _ = 1 := h⟩

/-- The specified Bézout witness also supplies the existing right-unimodular row predicate. -/
theorem isRightUnimodular_of_coefficientRowTwo (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    IsRightUnimodular a := by
  refine ⟨b, ?_⟩
  simpa [IsRightUnimodular, dotProduct, Fin.sum_univ_succ] using h

/-- A two-element row is right-unimodular exactly when its entries are
coprime in Mathlib's sense. -/
theorem isRightUnimodular_iff_isCoprime_two (R : Type u) [CommRing R]
    (a : Fin 2 → R) : IsRightUnimodular a ↔ IsCoprime (a 0) (a 1) := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b 0, b 1, ?_⟩
    calc
      b 0 * a 0 + b 1 * a 1 = a 0 * b 0 + a 1 * b 1 := by ring
      _ = 1 := by simpa [IsRightUnimodular, dotProduct, Fin.sum_univ_succ] using hb
  · rintro ⟨u, v, h⟩
    exact isRightUnimodular_of_coefficientRowTwo R a ![u, v] (by
      calc
        a 0 * u + a 1 * v = u * a 0 + v * a 1 := by ring
        _ = 1 := h)

/-- The second-coordinate map on the kernel of the first projection. -/
noncomputable def kernelProjZeroEquiv (R : Type u) [Semiring R] :
    LinearMap.ker (LinearMap.proj 0 : (Fin 2 → R) →ₗ[R] R) ≃ₗ[R] R := by
  letI : Unique {j : Fin 2 // j ≠ 0} :=
    { default := ⟨1, by decide⟩
      uniq := by
        rintro ⟨j, hj⟩
        fin_cases j
        · exact False.elim (hj rfl)
        · rfl }
  exact (coordinateHyperplaneEquiv R 2 0).trans
    (LinearEquiv.funUnique {j : Fin 2 // j ≠ 0} R R)

@[simp]
theorem kernelProjZeroEquiv_apply (R : Type u) [Semiring R]
    (x : LinearMap.ker (LinearMap.proj 0 : (Fin 2 → R) →ₗ[R] R)) :
    kernelProjZeroEquiv R x = x.1 1 := by
  simp only [kernelProjZeroEquiv, LinearEquiv.trans_apply, LinearEquiv.funUnique_apply]
  rfl

@[simp]
theorem kernelProjZeroEquiv_symm_apply (R : Type u) [Semiring R] (t : R) :
    ((kernelProjZeroEquiv R).symm t).1 = ![0, t] := by
  ext i
  fin_cases i
  · change ((kernelProjZeroEquiv R).symm t).1 0 = 0
    exact LinearMap.mem_ker.mp ((kernelProjZeroEquiv R).symm t).2
  · change ((kernelProjZeroEquiv R).symm t).1 1 = t
    exact (kernelProjZeroEquiv_apply R ((kernelProjZeroEquiv R).symm t)).symm.trans
      ((kernelProjZeroEquiv R).apply_symm_apply t)

/-- Explicit scalar coordinates on the kernel of a two-element coefficient row.
The inverse maps `t` to `(-a 1 * t, a 0 * t)`. -/
noncomputable def coefficientRowKernelEquivTwo (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    LinearMap.ker (coefficientRowScalarMap R 2 a) ≃ₗ[R] R :=
  (kernelEquivOfLinearEquiv (coefficientRowScalarMap R 2 a)
    (LinearMap.proj 0) (LinearEquiv.coefficientRowCompletionTwo R a b h)
    (fun x ↦ LinearEquiv.coefficientRowCompletionTwo_apply_zero R a b x h)).trans
    (kernelProjZeroEquiv R)

/-- A kernel element's scalar coordinate is the second completed-row coordinate. -/
@[simp]
theorem coefficientRowKernelEquivTwo_apply (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1)
    (x : LinearMap.ker (coefficientRowScalarMap R 2 a)) :
    coefficientRowKernelEquivTwo R a b h x = -b 1 * x.1 0 + b 0 * x.1 1 := by
  change (LinearEquiv.coefficientRowCompletionTwo R a b h x.1) 1 = _
  exact LinearEquiv.coefficientRowCompletionTwo_apply_one R a b x.1 h

/-- The scalar coordinate `t` corresponds to `(-a 1 * t, a 0 * t)`,
not to the second row of the completion. -/
@[simp]
theorem coefficientRowKernelEquivTwo_symm_apply (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) (t : R) :
    ((coefficientRowKernelEquivTwo R a b h).symm t).1 =
      ![-a 1 * t, a 0 * t] := by
  have hval : ((coefficientRowKernelEquivTwo R a b h).symm t).1 =
      (LinearEquiv.coefficientRowCompletionTwo R a b h).symm ![0, t] := by
    change (LinearEquiv.coefficientRowCompletionTwo R a b h).symm
      ((kernelProjZeroEquiv R).symm t).1 = _
    rw [kernelProjZeroEquiv_symm_apply]
  rw [hval]
  ext i
  fin_cases i
  · simp
  · simp

end Bass

namespace LinearEquiv

universe u v

/-- The first projection of a supplied product equivalence, as a linear map
on the original rank-two free module. -/
def coefficientProductFirstMap (R : Type u) [Semiring R]
    (P : Type v) [AddCommMonoid P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) : (Fin 2 → R) →ₗ[R] R :=
  (LinearMap.fst R R P).comp e.toLinearMap

@[simp]
theorem coefficientProductFirstMap_apply (R : Type u) [Semiring R]
    (P : Type v) [AddCommMonoid P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (x : Fin 2 → R) :
    coefficientProductFirstMap R P e x = (e x).1 := rfl

/-- The coefficients of the original first projection of a product equivalence. -/
def coefficientProductRow (R : Type u) [Semiring R]
    (P : Type v) [AddCommMonoid P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) : Fin 2 → R :=
  fun i ↦ coefficientProductFirstMap R P e (Pi.single i 1)

@[simp]
theorem coefficientProductRow_apply_basis (R : Type u) [Semiring R]
    (P : Type v) [AddCommMonoid P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (i : Fin 2) :
    coefficientProductRow R P e i = (e (Pi.single i 1)).1 := rfl

/-- Evaluation on the coordinate basis recovers the original first projection. -/
@[simp]
theorem coefficientProductRow_apply (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (x : Fin 2 → R) :
    Bass.coefficientRowScalarMap R 2 (coefficientProductRow R P e) x = (e x).1 := by
  have hsum := congrArg (coefficientProductFirstMap R P e) (pi_eq_sum_univ' x)
  simpa [Bass.coefficientRowScalarMap_apply, dotProduct, coefficientProductRow,
    map_sum, map_smul, smul_eq_mul, mul_comm] using hsum.symm

/-- The inverse image of `(1,0)` is a Bézout witness for the original projection. -/
theorem coefficientProductRow_witness (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) :
    let a := coefficientProductRow R P e
    let b := e.symm (1, 0)
    a 0 * b 0 + a 1 * b 1 = 1 := by
  simpa [Bass.coefficientRowScalarMap_apply, dotProduct, Fin.sum_univ_two] using
    (coefficientProductRow_apply R P e (e.symm (1, 0))).trans
      (by simp : (e (e.symm (1, 0))).1 = 1)

/-- The inverse image under `e` of `(0,p)` identifies `P` with the
kernel of the coefficient row recovered from `e`. -/
noncomputable def coefficientProductRowKernelEquiv (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) :
    P ≃ₗ[R] LinearMap.ker (Bass.coefficientRowScalarMap R 2 (coefficientProductRow R P e)) :=
  ((LinearEquiv.ofLeftInverse (f := LinearMap.inr R R P)
      (g := LinearMap.snd R R P) (by intro p; rfl)).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_inr R R P))).trans
    ((Bass.kernelEquivOfLinearEquiv
      (Bass.coefficientRowScalarMap R 2 (coefficientProductRow R P e))
      (LinearMap.fst R R P) e (fun x ↦ (coefficientProductRow_apply R P e x).symm)).symm)

/-- The kernel identification uses the *given* product equivalence. -/
@[simp]
theorem coefficientProductRowKernelEquiv_apply_val (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (p : P) :
    (coefficientProductRowKernelEquiv R P e p).1 = e.symm (0, p) := by
  rfl

/-- In the reverse direction, the kernel element is sent to the original
second projection. -/
@[simp]
theorem coefficientProductRowKernelEquiv_symm_apply (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P))
    (x : LinearMap.ker (Bass.coefficientRowScalarMap R 2 (coefficientProductRow R P e))) :
    (coefficientProductRowKernelEquiv R P e).symm x = (e x.1).2 := by
  rfl

/-- Cancellation from a *supplied* rank-two product equivalence, with no
freeness or invertibility assumption on `P`. -/
noncomputable def coefficientProductCancellationTwo (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) : P ≃ₗ[R] R :=
  (coefficientProductRowKernelEquiv R P e).trans
    (Bass.coefficientRowKernelEquivTwo R (coefficientProductRow R P e)
      (e.symm (1, 0)) (coefficientProductRow_witness R P e))

/-- Cancellation sends `p` to the second completed-row coordinate of
`e.symm (0,p)`. -/
@[simp]
theorem coefficientProductCancellationTwo_apply (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (p : P) :
    let x := e.symm (0, p)
    let b := e.symm (1, 0)
    coefficientProductCancellationTwo R P e p = -b 1 * x 0 + b 0 * x 1 := by
  simp only [coefficientProductCancellationTwo, LinearEquiv.trans_apply,
    Bass.coefficientRowKernelEquivTwo_apply, coefficientProductRowKernelEquiv_apply_val]

/-- The inverse cancellation map sends `t` through the kernel generator
and then through the supplied equivalence's second projection. -/
@[simp]
theorem coefficientProductCancellationTwo_symm_apply (R : Type u) [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P]
    (e : (Fin 2 → R) ≃ₗ[R] (R × P)) (t : R) :
    let a := coefficientProductRow R P e
    (coefficientProductCancellationTwo R P e).symm t =
      (e ![-a 1 * t, a 0 * t]).2 := by
  simp only [coefficientProductCancellationTwo, LinearEquiv.symm_trans_apply,
    Bass.coefficientRowKernelEquivTwo_symm_apply,
    coefficientProductRowKernelEquiv_symm_apply]

end LinearEquiv
