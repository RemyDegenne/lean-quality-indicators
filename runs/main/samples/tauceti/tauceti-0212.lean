public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane

namespace CompactConvexPolygon

variable {n : ℕ} [NeZero n] (P : CompactConvexPolygon n)

theorem interiorAngle_def (i : Fin n) :
    P.interiorAngle i =
      UpperHalfPlane.interiorAngle (P.vertex i) (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  rfl

end CompactConvexPolygon
end TauCeti.UpperHalfPlane
end
end
