@[expose] public section

section SourceQuantumWitness

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {ι σ X O K : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype X] [DecidableEq X] [DecidableEq O] [Fintype K] [DecidableEq K]

/-- A state of the construction's shape. -/
def scState (α : ℂ) (A : ι → σ → K → ℂ) : QBasis ι σ (Option K) → ℂ
  | (none, none, none) => α
  | (some i, some s, some k) => A i s k
  | _ => 0

end QuantumQueryComplexity
end SourceQuantumWitness
end
