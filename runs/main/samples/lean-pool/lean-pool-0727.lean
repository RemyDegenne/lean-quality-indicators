@[expose] public section

section SourceDefs

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

variable {O : Type*}

omit [DecidableEq ι] [DecidableEq σ] [Fintype ι] [Fintype σ] in
lemma isAdvMatrix_zero (f : (ι → σ) → O) : IsAdvMatrix f 0 :=
  ⟨Matrix.isHermitian_zero, fun _ _ _ => rfl⟩

end QuantumQueryComplexity
end SourceDefs
end
