namespace P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3200000

noncomputable section

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

universe u v w

section

section

set_option maxHeartbeats 25600000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

noncomputable section

p2m_open

p2m_open_scoped

namespace WeierstrassCurve

namespace Affine

p2m_open

p2m_open

variable {F : Type u} [Field F]

section PointPullbackTo

variable {W : Affine F} {L : Type*} [Field L] [Algebra F L]

def pointPullbackHomTo {xP yP : L}
    (h : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (hx : Function.Injective (Polynomial.aeval (R := F) xP)) :
    W.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (pointPullbackCoordHomTo_injective h hx)

end PointPullbackTo
end Affine
end WeierstrassCurve
end
end
end
end
end P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq
