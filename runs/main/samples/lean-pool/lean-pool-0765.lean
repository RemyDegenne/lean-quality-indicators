@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFairHistoryPriorWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    0 ≤ exactFairHistoryPriorWeight G n D r := by
  exact mul_nonneg (exactSeedWeight_nonneg r.seed)
    (exactRevealMass_nonneg G n D r.seed r.history)

end
end QuantumParallelRepetition
end
end
