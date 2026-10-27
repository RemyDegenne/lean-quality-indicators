@[expose] public section

noncomputable section

namespace NavierStokes.NaturalProfile

open Set Filter NaturalAxisBridge NaturalAxisCoefficients

open scoped Topology ContDiff

/-- Domain, given by `rescalePoint Λ ⁻¹' AxisEvaluation.strip window 20`. -/
def domain (Λ : ℝ) : Set (ℝ × ℝ) :=
  rescalePoint Λ ⁻¹' AxisEvaluation.strip window 20

end NavierStokes.NaturalProfile
end
end
