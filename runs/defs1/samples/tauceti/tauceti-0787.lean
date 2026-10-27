public section

noncomputable section

open UpperHalfPlane

open Matrix.ProjectiveSpecialLinearGroup (upperRightHom)

open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- The left half-plane bounded by `geodesicLine g`: the `g`-translate of the points with
negative real part. -/
def leftHalfPlane (g : PSL(2, ℝ)) : Set ℍ := g • {z : ℍ | z.re < 0}

end TauCeti.UpperHalfPlane
end
end
