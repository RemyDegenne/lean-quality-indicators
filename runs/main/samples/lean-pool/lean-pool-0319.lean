@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactRepeatedQuestionTail_splitAt_bob
    (G : Game X Y A B) (n : ℕ)
    (i : Fin n) (xs : Fin n → X)
    (y y' : Y) (tail : {j : Fin n // j ≠ i} → Y) :
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y, tail) j)) =
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y', tail) j)) := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  have different : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
    Equiv.coe_fn_mk, different, ↓reduceDIte]

end
end QuantumParallelRepetition
end
end
