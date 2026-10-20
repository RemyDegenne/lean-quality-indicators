@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

noncomputable local instance matrixComplexContinuousENormPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

noncomputable local instance matrixComplexESeminormedAddCommMonoidPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ESeminormedAddCommMonoid (Matrix m n ℂ) :=
  let base := @NormedAddCommGroup.toENormedAddCommMonoid (Matrix m n ℂ)
    Matrix.normedAddCommGroup
  { toContinuousENorm := inferInstance
    toAddCommMonoid := base.toAddCommMonoid
    enorm_zero := base.enorm_zero
    enorm_add_le := base.enorm_add_le }

attribute [instance] Strategy.aliceFintype Strategy.bobFintype
  Strategy.aliceDecidableEq Strategy.bobDecidableEq

section

open WithLp

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem diagonalSchmidtState_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) :
    ‖diagonalSchmidtState σ‖ ^ 2 =
      ∑ i : d, σ i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : d, ‖if i = j then (σ i : ℂ) else 0‖ ^ 2) =
      σ i ^ 2
  have hterm (j : d) :
      ‖if i = j then (σ i : ℂ) else 0‖ ^ 2 =
        if i = j then σ i ^ 2 else 0 := by
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

end
end QuantumParallelRepetition
end
end
