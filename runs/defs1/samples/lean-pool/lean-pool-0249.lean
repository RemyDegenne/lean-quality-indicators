@[expose] public section

section SourceQuantumClock

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {ι σ W : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  [Fintype W] [DecidableEq W] {T : ℕ}

/-- The reflection about the uniform-clock subspace. -/
noncomputable def clockRefl (T : ℕ) :
    Matrix (QBasis ι σ (ClockWork ι T W)) (QBasis ι σ (ClockWork ι T W)) ℂ :=
  qRefl (clockAvgProj T)

end QuantumQueryComplexity
end SourceQuantumClock
end
