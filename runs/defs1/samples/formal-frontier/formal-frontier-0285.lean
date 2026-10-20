@[expose] public section

universe uR uM

open CategoryTheory

namespace ModuleCat

variable (R : Type uR) [Ring R]

section CoefficientComparison

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The right dual restricted along the inverse double-opposite isomorphism
is linearly equivalent to the right-linear forms valued in `Rᵐᵒᵖ`. The
underlying additive operator and its inverse are those of
`LinearEquiv.rightDualOpposite`. -/
def rightDualRestrictScalarsEquiv (M : ModuleCat.{uM} Rᵐᵒᵖ) :
    ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).obj
      ((ModuleCat.rightDual R).obj (Opposite.op M))) ≃ₗ[Rᵐᵒᵖᵐᵒᵖ]
        (M →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) where
  toAddEquiv := (LinearEquiv.rightDualOpposite R M).toAddEquiv
  map_smul' := by
    intro a f
    change LinearEquiv.rightDualOpposite R M
        ((RingEquiv.opOp R).symm a • (show M →ₗ[Rᵐᵒᵖ] R from f)) =
      a • LinearEquiv.rightDualOpposite R M (show M →ₗ[Rᵐᵒᵖ] R from f)
    simpa only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] using
      (LinearEquiv.rightDualOpposite R M).map_smulₛₗ
        ((RingEquiv.opOp R).symm a) (show M →ₗ[Rᵐᵒᵖ] R from f)

end CoefficientComparison
end ModuleCat
end
