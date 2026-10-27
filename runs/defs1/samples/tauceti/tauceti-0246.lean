public section

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix

namespace TauCeti

variable (p : ℕ)

/-- The region of the lower-triangular coordinates with positive diagonal: the set underlying
`TauCeti.PosDiagLowerCoordinates`, and the set of coordinates of Cholesky factors. -/
def posDiagLowerRegion : Set (lowerTriangle p → ℝ) :=
  {x | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩}

end TauCeti
end
end
