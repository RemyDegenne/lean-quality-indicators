/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberKernels
public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation on native dual-number reduction kernels

The adjoint action on trace-zero matrices and the native group conjugation on the
first-order identity fibers use left conjugation, `g * X * g⁻¹`.
-/

@[expose] public section
set_option warningAsError true

universe u v w

namespace Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Matrix conjugation restricts to mathlib's trace-zero Lie algebra. -/
noncomputable def slAdjoint (g : Matrix.GeneralLinearGroup n R) :
    LieAlgebra.SpecialLinear.sl n R ≃ₗ⁅R⁆ LieAlgebra.SpecialLinear.sl n R := by
  let e := Matrix.lieConj (g : Matrix n n R) (g.invertible)
  apply e.ofSubalgebras _ _
  apply LieSubalgebra.ext
  intro X
  change X ∈ (LieAlgebra.SpecialLinear.sl n R).map (e : Matrix n n R →ₗ⁅R⁆ Matrix n n R) ↔
    X ∈ LieAlgebra.SpecialLinear.sl n R
  constructor
  · rintro ⟨Y, hY, rfl⟩
    change (e Y).trace = 0
    rw [Matrix.lieConj_apply, ← Matrix.coe_units_inv, Matrix.trace_units_conj]
    exact hY
  · intro hX
    refine ⟨e.symm X, ?_, e.apply_symm_apply X⟩
    change ((e.symm X)).trace = 0
    rw [Matrix.lieConj_symm_apply, ← Matrix.coe_units_inv, Matrix.trace_units_conj']
    exact hX

@[simp] theorem slAdjoint_val (g : Matrix.GeneralLinearGroup n R)
    (X : LieAlgebra.SpecialLinear.sl n R) :
    ((slAdjoint g X).1 : Matrix n n R) =
      (g : Matrix n n R) * X.1 * (g⁻¹ : Matrix.GeneralLinearGroup n R) := by
  simp [slAdjoint, Matrix.lieConj_apply, Matrix.coe_units_inv]

private def sndMatrix (A : Matrix n n (DualNumber R)) : Matrix n n R :=
  fun i j => (A i j).snd

omit [DecidableEq n] in
private theorem sndMatrix_mul (A B : Matrix n n (DualNumber R)) :
    sndMatrix (A * B) =
      A.map (DualNumber.fstRingHom R) * sndMatrix B +
        sndMatrix A * B.map (DualNumber.fstRingHom R) := by
  ext i j
  simp [sndMatrix, Matrix.mul_apply, TrivSqZeroExt.snd_sum,
    Finset.sum_add_distrib]

omit [Fintype n] in
private theorem sndMatrix_one :
    sndMatrix (1 : Matrix n n (DualNumber R)) = 0 := by
  ext i j
  by_cases hij : i = j <;> simp [sndMatrix, Matrix.one_apply, hij]

omit [Fintype n] in
private theorem sndMatrix_lift (X : Matrix n n R) : sndMatrix (liftMatrix X) = X := rfl

omit [Fintype n] in
private theorem fstMatrix_lift (X : Matrix n n R) :
    (liftMatrix X).map (DualNumber.fstRingHom R) = 1 := by
  ext i j
  exact liftMatrix_fst X i j

private theorem sndMatrix_conj_lift (h : Matrix.GeneralLinearGroup n (DualNumber R))
    (X : Matrix n n R) :
    sndMatrix ((h : Matrix n n (DualNumber R)) * liftMatrix X *
      ((h⁻¹ : Matrix.GeneralLinearGroup n (DualNumber R)) : Matrix n n (DualNumber R))) =
      ((glReduce R n h : Matrix.GeneralLinearGroup n R) : Matrix n n R) * X *
        (((glReduce R n h)⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R) := by
  let A : Matrix n n (DualNumber R) := h
  let B : Matrix n n (DualNumber R) :=
    ((h⁻¹ : Matrix.GeneralLinearGroup n (DualNumber R)) : Matrix n n (DualNumber R))
  have hAB : A * B = 1 := by simp [A, B]
  have hzero : A.map (DualNumber.fstRingHom R) * sndMatrix B +
      sndMatrix A * B.map (DualNumber.fstRingHom R) = 0 := by
    rw [← sndMatrix_mul, hAB, sndMatrix_one]
  have hcalc : sndMatrix (A * liftMatrix X * B) =
      (A.map (DualNumber.fstRingHom R) * X) * B.map (DualNumber.fstRingHom R) := by
    rw [sndMatrix_mul, sndMatrix_mul, Matrix.map_mul,
      fstMatrix_lift, sndMatrix_lift]
    simp only [mul_one, Matrix.add_mul, mul_assoc]
    calc
      _ = (A.map (DualNumber.fstRingHom R) * sndMatrix B +
            sndMatrix A * B.map (DualNumber.fstRingHom R)) +
            A.map (DualNumber.fstRingHom R) * (X * B.map (DualNumber.fstRingHom R)) := by
              abel
      _ = _ := by rw [hzero, zero_add]
  change sndMatrix (A * liftMatrix X * B) = _
  rw [hcalc]
  change ((Matrix.GeneralLinearGroup.map (DualNumber.fstRingHom R) h :
      Matrix.GeneralLinearGroup n R) : Matrix n n R) * X *
    ((Matrix.GeneralLinearGroup.map (DualNumber.fstRingHom R) h⁻¹ :
      Matrix.GeneralLinearGroup n R) : Matrix n n R) = _
  rw [Matrix.GeneralLinearGroup.map_inv]

/-- Reduction controls left conjugation on the actual native GL identity fiber. -/
theorem glKerEquiv_conj (h : Matrix.GeneralLinearGroup n (DualNumber R))
    (X : Multiplicative (Matrix n n R)) :
    MulAut.conjNormal h (glKerEquiv X) =
      glKerEquiv (Multiplicative.ofAdd
        (((glReduce R n h : Matrix.GeneralLinearGroup n R) : Matrix n n R) *
          Multiplicative.toAdd X *
          (((glReduce R n h)⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R))) := by
  have hreadback : glReadback (MulAut.conjNormal h (glKerEquiv X)) =
      ((glReduce R n h : Matrix.GeneralLinearGroup n R) : Matrix n n R) *
        Multiplicative.toAdd X *
        (((glReduce R n h)⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R) := by
    change sndMatrix ((h : Matrix n n (DualNumber R)) *
        liftMatrix (Multiplicative.toAdd X) *
        ((h⁻¹ : Matrix.GeneralLinearGroup n (DualNumber R)) : Matrix n n (DualNumber R))) = _
    exact sndMatrix_conj_lift h (Multiplicative.toAdd X)
  calc
    MulAut.conjNormal h (glKerEquiv X) =
        glKerEquiv (Multiplicative.ofAdd (glReadback (MulAut.conjNormal h (glKerEquiv X)))) := by
      exact ((glKerEquiv (R := R) (n := n)).apply_symm_apply _).symm
    _ = _ := by rw [hreadback]

/-- The second component of any native GL kernel element transforms by the reduced conjugator. -/
theorem glReadback_conj (h : Matrix.GeneralLinearGroup n (DualNumber R))
    (k : (glReduce R n).ker) :
    glReadback (MulAut.conjNormal h k) =
      ((glReduce R n h : Matrix.GeneralLinearGroup n R) : Matrix n n R) *
        glReadback k *
        (((glReduce R n h)⁻¹ : Matrix.GeneralLinearGroup n R) : Matrix n n R) := by
  obtain ⟨X, rfl⟩ := glKerEquiv.surjective k
  rw [glKerEquiv_conj]
  rfl

/-- Native SL kernel conjugation is the restriction of native GL kernel conjugation. -/
theorem slToGL_conj (t : Matrix.SpecialLinearGroup n (DualNumber R))
    (k : (slReduce R n).ker) :
    slToGL (MulAut.conjNormal t k) =
      MulAut.conjNormal (Matrix.SpecialLinearGroup.toGL t) (slToGL k) := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.toGL (t * k.1 * t⁻¹) =
    Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL k.1 *
      (Matrix.SpecialLinearGroup.toGL t)⁻¹
  simp

/-- The SL readback square is the adjoint action of the reduced SL matrix. -/
theorem slReadback_conj (t : Matrix.SpecialLinearGroup n (DualNumber R))
    (k : (slReduce R n).ker) :
    slReadback (MulAut.conjNormal t k) =
      slAdjoint (Matrix.SpecialLinearGroup.toGL (slReduce R n t)) (slReadback k) := by
  apply Subtype.ext
  change glReadback (slToGL (MulAut.conjNormal t k)) = _
  rw [slToGL_conj, glReadback_conj, slAdjoint_val]
  have ht : glReduce R n (Matrix.SpecialLinearGroup.toGL t) =
      Matrix.SpecialLinearGroup.toGL (slReduce R n t) := by
    apply Units.ext
    rfl
  rw [ht]
  rfl

/-- Ring-hom coefficient change commutes with native conjugation on the GL fiber. -/
theorem glKerMap_conj {S : Type w} [CommRing S] (f : R →+* S)
    (h : Matrix.GeneralLinearGroup n (DualNumber R)) (k : (glReduce R n).ker) :
    glKerMap f (MulAut.conjNormal h k) =
      MulAut.conjNormal (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) h)
        (glKerMap f k) := by
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) (h * k.1 * h⁻¹) =
    Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) h *
      Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) k.1 *
      (Matrix.GeneralLinearGroup.map (DualNumber.mapRingHom f) h)⁻¹
  simp

end Matrix.DualNumberKernels
