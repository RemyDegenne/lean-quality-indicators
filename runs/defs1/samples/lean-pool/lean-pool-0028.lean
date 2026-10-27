@[expose] public section

section SourceCompositionHat

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

open Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- BL Definition 19, uniform-alphabet form: the composed matrix. -/
noncomputable def compose (g : α → (β → Bool) → Bool)
    (Γf : Matrix (α → Bool) (α → Bool) ℝ)
    (M : α → Matrix (β → Bool) (β → Bool) ℝ) :
    Matrix ((α × β) → Bool) ((α × β) → Bool) ℝ :=
  composeE (cubeBlocks α β) g Γf M

end QuantumQueryComplexity
end SourceCompositionHat
end
