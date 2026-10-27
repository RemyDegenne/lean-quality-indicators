@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open WithLp

open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- Transpose every effect of a POVM to obtain the conjugate measurement. -/
def unconditionalConjugatePOVM
    {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (P : POVM A ι) : POVM A ι where
  effect a := (P.effect a).transpose
  positive a := (P.positive a).transpose
  complete := by
    classical
    rw [← Matrix.transpose_sum]
    rw [P.complete, Matrix.transpose_one]

end
end QuantumParallelRepetition
end
end
