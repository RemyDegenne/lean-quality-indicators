@[expose] public section

open MeasureTheory Complex Filter Topology Set InnerProductSpace

open scoped Real

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The quadratic form associated to an operator: x ↦ ⟪x, Sx⟫. -/
def quadForm (S : H →L[ℝ] H) (x : H) : ℝ := @inner ℝ H _ x (S x)

end
end
