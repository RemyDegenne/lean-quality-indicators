@[expose] public section

section SourceAndOr

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

open Matrix

/-- `β = 2^(1/4)`. -/
noncomputable def and2Beta : ℝ := Real.sqrt (Real.sqrt 2)

end QuantumQueryComplexity
end SourceAndOr
end
