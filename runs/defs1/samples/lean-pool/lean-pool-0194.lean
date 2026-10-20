@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.Pinsker

open QuantumParallelRepetition.ClassicalInformation

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The positive operator-valued measurement implementing exact source global catalyst alice. -/
def exactSourceGlobalCatalystAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalAlicePOVM G n S D a₀ x)))

end
end QuantumParallelRepetition
end
end
