section

@[expose] public section

noncomputable section

namespace NavierStokes.SubcoverPeriodicity

open Set Function CommonCoverSolve TorusInverse HarmonicCalculus ParticularWaveBounds

open scoped Topology BigOperators

section SubcoverFields

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
omit [NormedAddCommGroup P] in
theorem commonPressure_subcover_shift (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (κ : Plane → ℝ) (frequency : ℝ) (d : ℕ) (k : Frequency) (p : P)
    (hf : ∀ Y : Plane,
      f (p, Y + TorusAverages.latticePoint (coverIndex d k)) = f (p,Y)) (Y : Plane) :
    commonPressure t f g hab κ frequency (p, Y + TorusAverages.latticePoint (coverIndex d k)) =
      commonPressure t f g hab κ frequency (p,Y) :=
  commonPressure_shift t f g hab κ frequency (coverIndex d k) p hf Y

end SubcoverFields
end NavierStokes.SubcoverPeriodicity
end
end
end
