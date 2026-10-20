public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- Nonzero triangle determinant gives an invertible real continuous linear coordinate map. -/
def triangleCoordinates (c p q : ℂ) (hdet : triangleDet c p q ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ((triangleLinearMap c p q).equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr ((det_triangleLinearMap c p q).trans_ne hdet))).toContinuousLinearEquiv

end TauCeti.Green
end
end
