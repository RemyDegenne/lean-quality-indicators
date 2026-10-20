public section

open Polynomial

namespace WeierstrassCurve.Affine.FunctionField

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve.Affine R)

variable (L : Type*) [Field L] [Algebra R[X] L] [IsFractionRing R[X] L]
  [Algebra L W.FunctionField] [IsScalarTower R[X] L W.FunctionField]

theorem basis_apply (i : Fin 2) :
    basis W L i = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.basis W i) := by
  simp [basis, coe_basisOfLinearIndependentOfCardEqFinrank]

end WeierstrassCurve.Affine.FunctionField
end
