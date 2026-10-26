/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import NormForms.FiniteFieldFormZeros

/-!
# Annihilating tensors by a common scalar sum

A nonzero linear combination of the projections from a finite product onto a module
is surjective. For positive tensor powers, a dimension bound on the target alone
produces a common nonzero combination annihilating any finite family of tensors.
-/

set_option warningAsError true

@[expose] public section

namespace TensorPower

open scoped TensorProduct

variable {K ι M N : Type*} [Field K] [Fintype ι]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The linear combination of the coordinate projections with coefficients `a`. -/
noncomputable def scalarSum (a : ι → K) : (ι → M) →ₗ[K] M :=
  ∑ i : ι, a i • LinearMap.proj i

@[simp]
theorem scalarSum_apply (a : ι → K) (v : ι → M) :
    scalarSum (M := M) a v = ∑ i : ι, a i • v i := by
  simp [scalarSum]

/-- A nonzero coefficient vector makes the scalar sum surjective. -/
theorem scalarSum_surjective_of_ne_zero (a : ι → K) (ha : a ≠ 0) :
    Function.Surjective (scalarSum (M := M) a) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    have h : ∀ j, a j = 0 := by simpa only [not_exists, not_not] using h
    apply ha
    exact funext (fun j => h j)
  intro m
  refine ⟨fun j => if j = i then (a i)⁻¹ • m else 0, ?_⟩
  simp [scalarSum_apply, Finset.sum_ite_eq', hi]

/-- Tensor the scalar sum in each slot, then tensor its result with the identity on `N`. -/
noncomputable def scalarSumTensor (s : ℕ) (a : ι → K) :
    (TensorPower K s (ι → M)) ⊗[K] N →ₗ[K] (TensorPower K s M) ⊗[K] N :=
  (PiTensorProduct.map (fun _ : Fin s => scalarSum (M := M) a)).rTensor N

private noncomputable def tensorEvaluation (s : ℕ)
    (z : (TensorPower K s (ι → M)) ⊗[K] N) :
    MultilinearMap K (fun _ : Fin s => (ι → M) →ₗ[K] M)
      ((TensorPower K s M) ⊗[K] N) :=
  ((LinearMap.applyₗ (R := K) z).comp (LinearMap.rTensorHom N)).compMultilinearMap
    (PiTensorProduct.mapMultilinear K (fun _ : Fin s => ι → M) (fun _ => M))

private theorem tensorEvaluation_apply (s : ℕ)
    (z : (TensorPower K s (ι → M)) ⊗[K] N) (a : ι → K) :
    tensorEvaluation (M := M) s z (fun _ => scalarSum (M := M) a) =
      scalarSumTensor (M := M) s a z := rfl

private theorem scalarSumTensor_expand (s : ℕ)
    (z : (TensorPower K s (ι → M)) ⊗[K] N) (a : ι → K) :
    scalarSumTensor (M := M) s a z =
      ∑ u : Fin s → ι, (∏ k : Fin s, a (u k)) •
        tensorEvaluation (M := M) s z (fun k => LinearMap.proj (R := K) (u k)) := by
  classical
  rw [← tensorEvaluation_apply]
  change tensorEvaluation (M := M) s z (fun _ : Fin s =>
    ∑ i : ι, a i • LinearMap.proj i) = _
  rw [(tensorEvaluation (M := M) s z).map_sum
    (fun _ : Fin s => fun i : ι => a i • LinearMap.proj i)]
  congr 1
  funext u
  exact (tensorEvaluation (M := M) s z).map_smul_univ
    (fun k => a (u k)) (fun k => LinearMap.proj (R := K) (u k))

private noncomputable def scalarSumCoordinatePolynomial (s : ℕ)
    [FiniteDimensional K ((TensorPower K s M) ⊗[K] N)]
    (z : (TensorPower K s (ι → M)) ⊗[K] N)
    (q : Fin (Module.finrank K ((TensorPower K s M) ⊗[K] N))) :
    MvPolynomial ι K :=
  let b := Module.finBasis K ((TensorPower K s M) ⊗[K] N)
  ∑ u : Fin s → ι,
    MvPolynomial.C (b.coord q (tensorEvaluation (M := M) s z
      (fun k => LinearMap.proj (R := K) (u k)))) *
      ∏ k : Fin s, MvPolynomial.X (u k)

private theorem scalarSumCoordinatePolynomial_homogeneous (s : ℕ)
    [FiniteDimensional K ((TensorPower K s M) ⊗[K] N)]
    (z : (TensorPower K s (ι → M)) ⊗[K] N)
    (q : Fin (Module.finrank K ((TensorPower K s M) ⊗[K] N))) :
    (scalarSumCoordinatePolynomial (M := M) s z q).IsHomogeneous s := by
  classical
  unfold scalarSumCoordinatePolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro u _
  have hprod : (∏ k : Fin s, (MvPolynomial.X (u k) : MvPolynomial ι K)).IsHomogeneous s := by
    convert MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun k : Fin s => (MvPolynomial.X (u k) : MvPolynomial ι K))
      (fun _ : Fin s => 1)
      (by intro k _; exact MvPolynomial.isHomogeneous_X K (u k)) using 1; simp
  exact hprod.C_mul _

private theorem scalarSumCoordinatePolynomial_eval (s : ℕ)
    [FiniteDimensional K ((TensorPower K s M) ⊗[K] N)]
    (z : (TensorPower K s (ι → M)) ⊗[K] N)
    (q : Fin (Module.finrank K ((TensorPower K s M) ⊗[K] N))) (a : ι → K) :
    MvPolynomial.eval a (scalarSumCoordinatePolynomial (M := M) s z q) =
      (Module.finBasis K ((TensorPower K s M) ⊗[K] N)).coord q
        (scalarSumTensor (M := M) s a z) := by
  classical
  rw [scalarSumTensor_expand]
  simp [scalarSumCoordinatePolynomial, map_sum, map_smul, smul_eq_mul, mul_comm]

/-- When the target tensor space is finite-dimensional, a positive tensor power
and a strict dimension bound admit a single surjective scalar sum whose induced
tensor map annihilates any prescribed finite family of tensors. No finiteness
assumption on either factor or the source tensor space is needed. -/
theorem exists_nonzero_scalarSumTensor_annihilates [Finite K] {τ : Type*} [Fintype τ]
    (s : ℕ) [FiniteDimensional K ((TensorPower K s M) ⊗[K] N)]
    (hs : 0 < s) (z : τ → (TensorPower K s (ι → M)) ⊗[K] N)
    (h : s * Fintype.card τ * Module.finrank K ((TensorPower K s M) ⊗[K] N) <
      Fintype.card ι) :
    ∃ a : ι → K, a ≠ 0 ∧ Function.Surjective (scalarSum (M := M) a) ∧
      ∀ j : τ, scalarSumTensor (M := M) s a (z j) = 0 := by
  classical
  let f : τ × Fin (Module.finrank K ((TensorPower K s M) ⊗[K] N)) → MvPolynomial ι K :=
    fun e => scalarSumCoordinatePolynomial (M := M) s (z e.1) e.2
  have hdegree : (∑ _ : τ × Fin (Module.finrank K ((TensorPower K s M) ⊗[K] N)), s) <
      Fintype.card ι := by
    calc
      _ = s * Fintype.card τ * Module.finrank K ((TensorPower K s M) ⊗[K] N) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fin]
        ac_rfl
      _ < Fintype.card ι := h
  obtain ⟨a, ha, hzero⟩ :=
    MvPolynomial.exists_nonzero_common_zero_of_sum_degrees_lt
      (fun _ : τ × Fin (Module.finrank K ((TensorPower K s M) ⊗[K] N)) => s)
      (fun _ => hs) f
      (fun e => scalarSumCoordinatePolynomial_homogeneous s (z e.1) e.2) hdegree
  refine ⟨a, ha, scalarSum_surjective_of_ne_zero a ha, ?_⟩
  intro j
  apply (Module.finBasis K ((TensorPower K s M) ⊗[K] N)).forall_coord_eq_zero_iff.mp
  intro q
  rw [← scalarSumCoordinatePolynomial_eval s (z j) q a]
  exact hzero ⟨j, q⟩

end TensorPower

end
