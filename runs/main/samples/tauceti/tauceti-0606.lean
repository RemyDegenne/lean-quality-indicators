public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable [Field K] [Algebra R K] [IsFractionRing R K]

namespace Model

@[simp]
lemma genericι_projectiveLine :
    (projectiveLine R K).genericι =
      AlgebraicGeometry.projectiveLine.baseChangeProjection R K ≫
        eqToHom (projectiveLine_total R K).symm := by
  simp [genericι_def, projectiveLine, projectiveLineGenericFiberIso_inv_left]

end Model
end TauCeti
end
end
