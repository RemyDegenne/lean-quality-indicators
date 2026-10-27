public section

open Polynomial TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]
  (Φ : AddSubgroup (W⁄F).toAffine.Point) [Finite Φ]

/-- **The Vélu isogeny** `W → W / Φ`: the coordinate pullback sending the coordinates of the
quotient curve `veluCurve W Φ` to Vélu's coordinates `veluX W Φ` and `veluY W Φ`. -/
noncomputable def veluIsogeny : Isogeny W (veluCurve W Φ).toAffine where
  pullback := (functionFieldLift (equation_veluX_veluY W Φ) (transcendental_veluX W Φ)).comp
    (IsScalarTower.toAlgHom F _ _)
  mapsInfinity := by
    refine CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace _
      (algebraMap F[X] (veluCurve W Φ).toAffine.CoordinateRing Polynomial.X) ?_
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply,
      ← genericX_eq_algebraMap, functionFieldLift_genericX, infinityPlace_veluX,
      ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

end WeierstrassCurve.Affine
end
