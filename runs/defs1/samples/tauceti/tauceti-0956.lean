public section

open Polynomial

open scoped Polynomial.Bivariate

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F]

namespace Isogeny

/-- The identity isogeny. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : Isogeny W W where
  pullback := CoordinatePullback.id W
  mapsInfinity := (CoordinatePullback.mapsInfinity_iff _).2
    (CoordinatePullback.mapsInfinity_id W)

end Isogeny
end TauCeti
end
