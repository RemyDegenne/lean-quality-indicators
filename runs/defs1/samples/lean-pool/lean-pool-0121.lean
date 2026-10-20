universe u v

open scoped DirectSum TensorProduct

public noncomputable section

namespace LoweringDerivation

variable {E : Type u} {R : Type v} [Field E] [CommRing R] [Algebra E R]

variable (𝒜 : NatOrdinal → Submodule E R) [GradedAlgebra 𝒜]

/-- The inclusion `A_j → A_{<ω}`. -/
def natInclusion (j : ℕ) : 𝒜 (j : NatOrdinal) →ₗ[E] finiteDegreePart 𝒜 where
  toFun a := ⟨a, mem_finiteDegreePart_of_mem 𝒜 a.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LoweringDerivation
end
