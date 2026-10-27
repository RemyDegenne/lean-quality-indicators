@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open scoped BigOperators

/-- The has subexponential witness construction used in the quantum parallel-repetition argument. -/
def HasSubexponentialWitness (v : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ C : ℝ, 0 < C →
    ∃ n : ℕ, C * Real.exp (-c * (n : ℝ)) < v n

end
end QuantumParallelRepetition
end
end
