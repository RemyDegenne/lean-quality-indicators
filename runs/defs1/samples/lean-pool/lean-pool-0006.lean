@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

noncomputable local instance matrixComplexContinuousENormPartTwo
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open WithLp

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The unitary operator implementing controlled finite tensor local. -/
def controlledFiniteTensorLocalUnitary
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun ω => finiteTensorLocalUnitary (U ω))

end
end QuantumParallelRepetition
end
end
