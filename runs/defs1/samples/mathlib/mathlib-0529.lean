@[expose] public section

open Function Set Filter Bornology Metric Pointwise Topology

section Operations

variable {R₁ R₄ : Type*} [Semiring R₁] [CommSemiring R₄]
  {σ₁₄ : R₁ →+* R₄} {M₁ M₂ M₄ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [TopologicalSpace M₄] [AddCommGroup M₄]

variable (σ₁₄ M₁ M₄)

/-- The submodule of compact continuous linear maps. -/
def compactOperator [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
    [IsTopologicalAddGroup M₄] : Submodule R₄ (M₁ →SL[σ₁₄] M₄) where
  carrier := { f | IsCompactOperator f }
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

end Operations
end
