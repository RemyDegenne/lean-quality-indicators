public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups Pointwise OnePoint Real

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-- The centre on the real axis of the semicircle through `P` and `Q`, when `P.re ≠ Q.re`. -/
def circleCenter (P Q : ℍ) : ℝ :=
  (Complex.normSq (Q : ℂ) - Complex.normSq (P : ℂ)) / (2 * (Q.re - P.re))

end UpperHalfPlane
end
end
