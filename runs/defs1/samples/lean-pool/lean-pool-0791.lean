@[expose] public section

section SourceQuantumLowerBoundProgress

namespace QuantumQueryComplexity

open scoped Matrix Matrix.Norms.L2Operator

open Matrix

variable {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

variable {X : Type} [Fintype X] [DecidableEq X]

variable {W : Type} [Fintype W] [DecidableEq W]

variable {H : Type} [Fintype H] [DecidableEq H]

section Query

variable (read : X → ι → σ) (Γ : Matrix X X ℝ) (δ : X → ℝ)
  (ψ : X → (QBasis ι σ W → ℂ))

/-- The weight carried by the sector `o`. -/
noncomputable def sectorWeight (δ : X → ℝ) (ψ : X → (QBasis ι σ W → ℂ))
    (o : Option ι) : ℝ :=
  ∑ x, qNormSq (sectFam o δ ψ x)

end Query
end QuantumQueryComplexity
end SourceQuantumLowerBoundProgress
end
