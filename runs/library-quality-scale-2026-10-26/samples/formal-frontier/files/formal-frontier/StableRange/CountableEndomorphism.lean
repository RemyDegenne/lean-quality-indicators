/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import StableRange.RightRowCompletion
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# A countable endomorphism ring with a free unary-row kernel

The finitely supported module on the naturals splits into its even and odd
coordinates. Its endomorphism ring has a right-unimodular unary row with a
nonzero free right-coefficient kernel and a rectangular, but not square,
completion. The splitting works over any semiring and module with additive
inverses; nonzero obstructions additionally require a nontrivial module.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  I.1.2.1 (the infinite-dimensional endomorphism example and right-row motivation).
* Mathlib, `Finsupp.domLCongr`, `Finsupp.sumFinsuppLEquivProdFinsupp`,
  `Equiv.natSumNatEquivNat` and `Matrix.square_of_invertible`.
* `StableRange.RightRowCompletion`, for the right-coefficient kernel equivalence
  of a row in a rectangular two-sided inverse.
-/

set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

/-- The even and odd coordinates of a finitely supported sequence. -/
noncomputable def parityEquiv : (ℕ →₀ M) ≃ₗ[S] (ℕ →₀ M) × (ℕ →₀ M) :=
  (Finsupp.domLCongr (R := S) (M := M) Equiv.natSumNatEquivNat.symm).trans
    (Finsupp.sumFinsuppLEquivProdFinsupp S)

/-- Embed a finitely supported sequence into the even coordinates. -/
noncomputable def x₀ : Module.End S (ℕ →₀ M) :=
  (parityEquiv S M).symm.toLinearMap.comp (LinearMap.inl S (ℕ →₀ M) (ℕ →₀ M))

/-- Embed a finitely supported sequence into the odd coordinates. -/
noncomputable def x₁ : Module.End S (ℕ →₀ M) :=
  (parityEquiv S M).symm.toLinearMap.comp (LinearMap.inr S (ℕ →₀ M) (ℕ →₀ M))

/-- Extract the even coordinates of a finitely supported sequence. -/
noncomputable def y₀ : Module.End S (ℕ →₀ M) :=
  (LinearMap.fst S (ℕ →₀ M) (ℕ →₀ M)).comp (parityEquiv S M).toLinearMap

/-- Extract the odd coordinates of a finitely supported sequence. -/
noncomputable def y₁ : Module.End S (ℕ →₀ M) :=
  (LinearMap.snd S (ℕ →₀ M) (ℕ →₀ M)).comp (parityEquiv S M).toLinearMap

@[simp]
theorem parityEquiv_x₀ (v : ℕ →₀ M) : parityEquiv S M (x₀ S M v) = (v, 0) := by
  simp [x₀]

@[simp]
theorem parityEquiv_x₁ (v : ℕ →₀ M) : parityEquiv S M (x₁ S M v) = (0, v) := by
  simp [x₁]

@[simp]
theorem parityEquiv_fst_apply (v : ℕ →₀ M) (n : ℕ) :
    (parityEquiv S M v).1 n = v (2 * n) := by
  simp [parityEquiv, Finsupp.equivMapDomain_apply,
    Equiv.natSumNatEquivNat_apply]

@[simp]
theorem parityEquiv_snd_apply (v : ℕ →₀ M) (n : ℕ) :
    (parityEquiv S M v).2 n = v (2 * n + 1) := by
  simp [parityEquiv, Finsupp.equivMapDomain_apply,
    Equiv.natSumNatEquivNat_apply]

@[simp]
theorem parityEquiv_symm_apply_even (pair : (ℕ →₀ M) × (ℕ →₀ M)) (n : ℕ) :
    (parityEquiv S M).symm pair (2 * n) = pair.1 n := by
  have coordinate := parityEquiv_fst_apply S M ((parityEquiv S M).symm pair) n
  simpa using coordinate.symm

@[simp]
theorem parityEquiv_symm_apply_odd (pair : (ℕ →₀ M) × (ℕ →₀ M)) (n : ℕ) :
    (parityEquiv S M).symm pair (2 * n + 1) = pair.2 n := by
  have coordinate := parityEquiv_snd_apply S M ((parityEquiv S M).symm pair) n
  simpa using coordinate.symm

@[simp]
theorem y₀_apply (v : ℕ →₀ M) (n : ℕ) : y₀ S M v n = v (2 * n) := by
  simp [y₀]

@[simp]
theorem y₁_apply (v : ℕ →₀ M) (n : ℕ) : y₁ S M v n = v (2 * n + 1) := by
  simp [y₁]

@[simp]
theorem x₀_apply_even (v : ℕ →₀ M) (n : ℕ) : x₀ S M v (2 * n) = v n := by
  have coordinate := congrArg (fun pair : (ℕ →₀ M) × (ℕ →₀ M) => pair.1 n)
    (parityEquiv_x₀ S M v)
  simpa only [parityEquiv_fst_apply, Prod.fst] using coordinate

@[simp]
theorem x₀_apply_odd (v : ℕ →₀ M) (n : ℕ) : x₀ S M v (2 * n + 1) = 0 := by
  have coordinate := congrArg (fun pair : (ℕ →₀ M) × (ℕ →₀ M) => pair.2 n)
    (parityEquiv_x₀ S M v)
  simpa only [parityEquiv_snd_apply, Prod.snd, Finsupp.zero_apply] using coordinate

@[simp]
theorem x₁_apply_even (v : ℕ →₀ M) (n : ℕ) : x₁ S M v (2 * n) = 0 := by
  have coordinate := congrArg (fun pair : (ℕ →₀ M) × (ℕ →₀ M) => pair.1 n)
    (parityEquiv_x₁ S M v)
  simpa only [parityEquiv_fst_apply, Prod.fst, Finsupp.zero_apply] using coordinate

@[simp]
theorem x₁_apply_odd (v : ℕ →₀ M) (n : ℕ) : x₁ S M v (2 * n + 1) = v n := by
  have coordinate := congrArg (fun pair : (ℕ →₀ M) × (ℕ →₀ M) => pair.2 n)
    (parityEquiv_x₁ S M v)
  simpa only [parityEquiv_snd_apply, Prod.snd] using coordinate

/-- Extraction after insertion into the even coordinates is the identity. -/
theorem y₀_mul_x₀ : y₀ S M * x₀ S M = 1 := by
  ext v n
  simp [Module.End.mul_apply]

/-- Extraction of odd coordinates after even insertion vanishes. -/
theorem y₁_mul_x₀ : y₁ S M * x₀ S M = 0 := by
  ext v n
  simp [Module.End.mul_apply]

/-- Extraction of even coordinates after odd insertion vanishes. -/
theorem y₀_mul_x₁ : y₀ S M * x₁ S M = 0 := by
  ext v n
  simp [Module.End.mul_apply]

/-- Extraction after insertion into the odd coordinates is the identity. -/
theorem y₁_mul_x₁ : y₁ S M * x₁ S M = 1 := by
  ext v n
  simp [Module.End.mul_apply]

/-- Even and odd insertion after extraction reassemble the sequence. -/
theorem x₀_mul_y₀_add_x₁_mul_y₁ : x₀ S M * y₀ S M + x₁ S M * y₁ S M = 1 := by
  apply LinearMap.ext
  intro v
  apply (parityEquiv S M).injective
  simp [Module.End.mul_apply, LinearMap.add_apply, y₀, y₁]

/-- The unary row given by extracting even coordinates. -/
noncomputable def row : Fin 1 → Module.End S (ℕ →₀ M) := fun _ => y₀ S M

/-- The specified right inverse column for the even-coordinate row. -/
noncomputable def rightWitness : Fin 1 → Module.End S (ℕ →₀ M) := fun _ => x₀ S M

@[simp]
theorem row_zero : row S M 0 = y₀ S M := rfl

@[simp]
theorem rightWitness_zero : rightWitness S M 0 = x₀ S M := rfl

/-- The specified column is a right inverse to the original coefficient row. -/
theorem rightInverse :
    dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
      (row S M) (rightWitness S M) = 1 := by
  simpa [dotProductBilin, dotProduct, row, rightWitness, Fin.sum_univ_succ] using
    (y₀_mul_x₀ S M)

/-- The even-coordinate row is right-unimodular with its specified witness. -/
theorem rightUnimodular : Bass.IsRightUnimodular (row S M) := by
  exact ⟨rightWitness S M, rightInverse S M⟩

/-- The two-row matrix of even and odd projections. -/
noncomputable def rectangularRow :
    Matrix (Fin 2) (Fin 1) (Module.End S (ℕ →₀ M)) :=
  fun i _ => Fin.cases (y₀ S M) (fun _ => y₁ S M) i

/-- The two-column matrix of even and odd embeddings. -/
noncomputable def rectangularColumn :
    Matrix (Fin 1) (Fin 2) (Module.End S (ℕ →₀ M)) :=
  fun _ i => Fin.cases (x₀ S M) (fun _ => x₁ S M) i

@[simp]
theorem rectangularRow_zero_zero : rectangularRow S M 0 0 = y₀ S M := rfl

@[simp]
theorem rectangularRow_one_zero : rectangularRow S M 1 0 = y₁ S M := rfl

@[simp]
theorem rectangularColumn_zero_zero : rectangularColumn S M 0 0 = x₀ S M := rfl

@[simp]
theorem rectangularColumn_zero_one : rectangularColumn S M 0 1 = x₁ S M := rfl

/-- The first row of the rectangular matrix is the original unary row. -/
theorem rectangularRow_first : rectangularRow S M 0 = row S M := rfl

/-- The projection and insertion matrices compose to the identity on two coordinates. -/
theorem rectangularRow_mul_rectangularColumn :
    rectangularRow S M * rectangularColumn S M = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, y₀_mul_x₀, y₁_mul_x₀,
      y₀_mul_x₁, y₁_mul_x₁]

/-- The insertion and projection matrices compose to the identity on one coordinate. -/
theorem rectangularColumn_mul_rectangularRow :
    rectangularColumn S M * rectangularRow S M = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i; fin_cases j
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using x₀_mul_y₀_add_x₁_mul_y₁ S M

/-- Kernel coordinates for the original unary right-coefficient functional,
obtained from its specified rectangular two-sided inverse. -/
noncomputable def kernelEquiv :
    LinearMap.ker
        (dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
          (row S M)) ≃ₗ[(Module.End S (ℕ →₀ M))ᵐᵒᵖ]
      (Fin 1 → Module.End S (ℕ →₀ M)) :=
  LinearEquiv.rightCoefficientKernelEquivOfMatrixInverse
    (Module.End S (ℕ →₀ M)) (row S M) (rectangularRow S M)
    (rectangularColumn S M) (rectangularRow_first S M)
    (rectangularRow_mul_rectangularColumn S M)
    (rectangularColumn_mul_rectangularRow S M)

/-- The kernel coordinate of a right coefficient column is its odd projection. -/
theorem kernelEquiv_apply_zero
    (k : LinearMap.ker
      (dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
        (row S M))) :
    kernelEquiv S M k 0 = y₁ S M * k.1 0 := by
  change (rectangularRow S M *ᵥ k.1) 1 = _
  simp [Matrix.mulVec, dotProduct]

/-- The right coefficient column corresponding to a kernel coordinate is
obtained by inserting that coordinate into the odd positions. -/
theorem kernelEquiv_symm_apply_zero (r : Module.End S (ℕ →₀ M)) :
    ((kernelEquiv S M).symm (fun _ : Fin 1 => r)).1 0 = x₁ S M * r := by
  change (rectangularColumn S M *ᵥ Fin.cons 0 (fun _ : Fin 1 => r)) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The original right-coefficient kernel is free of rank one. -/
theorem free_kernel :
    Module.Free (Module.End S (ℕ →₀ M))ᵐᵒᵖ
      (LinearMap.ker
        (dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
          (row S M))) := by
  have h := (Matrix.isRightUnimodular_and_free_kernel_iff_exists_rectangular_inverse
    (Module.End S (ℕ →₀ M)) (row S M)).mpr
      ⟨1, rectangularRow S M, rectangularColumn S M,
        rectangularRow_first S M, rectangularRow_mul_rectangularColumn S M,
        rectangularColumn_mul_rectangularRow S M⟩
  exact h.2

/-- The rectangular two-sided inverse disproves invariant basis number even for the zero module. -/
theorem not_invariantBasisNumber :
    ¬ InvariantBasisNumber (Module.End S (ℕ →₀ M)) := by
  intro h
  have hdim := (invariantBasisNumber_iff_matrix (R := Module.End S (ℕ →₀ M))).mp h
    2 1 (rectangularRow S M) (rectangularColumn S M)
    (rectangularRow_mul_rectangularColumn S M)
    (rectangularColumn_mul_rectangularRow S M)
  omega

variable [Nontrivial M]

private theorem x₁_ne_zero : x₁ S M ≠ 0 := by
  obtain ⟨value, hvalue⟩ := exists_ne (0 : M)
  intro hzero
  have hcoordinate := x₁_apply_odd S M (Finsupp.single 0 value) 0
  simp only [hzero, LinearMap.zero_apply, Finsupp.zero_apply,
    Finsupp.single_eq_same] at hcoordinate
  exact hvalue hcoordinate.symm

/-- The original coefficient kernel contains a nonzero right coefficient column. -/
theorem kernel_nonzero :
    ∃ k : LinearMap.ker
      (dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
        (row S M)), k ≠ 0 := by
  refine ⟨(kernelEquiv S M).symm
    (fun _ : Fin 1 => (1 : Module.End S (ℕ →₀ M))), ?_⟩
  intro hzero
  apply x₁_ne_zero S M
  calc
    x₁ S M = ((kernelEquiv S M).symm
      (fun _ : Fin 1 => (1 : Module.End S (ℕ →₀ M)))).1 0 := by
        simpa using (kernelEquiv_symm_apply_zero S M (1 : Module.End S (ℕ →₀ M))).symm
    _ = 0 := by rw [hzero]; rfl

/-- Extraction of even coordinates is a split epimorphism but not a unit. -/
theorem not_isUnit_y₀ : ¬ IsUnit (y₀ S M) := by
  intro hunit
  obtain ⟨inverse, _, hleft⟩ := isUnit_iff_exists.mp hunit
  apply x₁_ne_zero S M
  calc
    x₁ S M = (inverse * y₀ S M) * x₁ S M := by rw [hleft, one_mul]
    _ = inverse * (y₀ S M * x₁ S M) := by rw [mul_assoc]
    _ = 0 := by rw [y₀_mul_x₁, mul_zero]

/-- No square unit has the given original unary row as its first row,
regardless of its inverse column. -/
theorem no_square_completion :
    ¬ ∃ g : Matrix.GeneralLinearGroup (Fin 1) (Module.End S (ℕ →₀ M)),
      (g : Matrix (Fin 1) (Fin 1) (Module.End S (ℕ →₀ M))) 0 = row S M := by
  rintro ⟨g, hrow⟩
  have hentry : (g : Matrix (Fin 1) (Fin 1) (Module.End S (ℕ →₀ M))) 0 0 =
      y₀ S M := by simpa using congrFun hrow 0
  apply not_isUnit_y₀ S M
  rw [← hentry]
  apply isUnit_iff_exists.mpr
  refine ⟨((g⁻¹ : Matrix.GeneralLinearGroup (Fin 1) (Module.End S (ℕ →₀ M))) :
    Matrix (Fin 1) (Fin 1) (Module.End S (ℕ →₀ M))) 0 0, ?_, ?_⟩
  · have h := congrArg
      (fun matrix : Matrix (Fin 1) (Fin 1) (Module.End S (ℕ →₀ M)) => matrix 0 0)
      g.val_inv
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h
  · have h := congrArg
      (fun matrix : Matrix (Fin 1) (Fin 1) (Module.End S (ℕ →₀ M)) => matrix 0 0)
      g.inv_val
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using h

/-- A right-unimodular unary row has a free, nonzero kernel yet admits no
square completion without invariant basis number. -/
theorem rightUnimodular_free_kernel_no_square :
    Bass.IsRightUnimodular (row S M) ∧
      Module.Free (Module.End S (ℕ →₀ M))ᵐᵒᵖ
        (LinearMap.ker
          (dotProductBilin (Module.End S (ℕ →₀ M))
            (Module.End S (ℕ →₀ M))ᵐᵒᵖ (row S M))) ∧
      (∃ k : LinearMap.ker
        (dotProductBilin (Module.End S (ℕ →₀ M))
          (Module.End S (ℕ →₀ M))ᵐᵒᵖ (row S M)), k ≠ 0) ∧
      ¬ ∃ g : Matrix.GeneralLinearGroup (Fin 1) (Module.End S (ℕ →₀ M)),
        (g : Matrix (Fin 1) (Fin 1) (Module.End S (ℕ →₀ M))) 0 = row S M := by
  exact ⟨rightUnimodular S M, free_kernel S M, kernel_nonzero S M,
    no_square_completion S M⟩

end CountableEndomorphism
