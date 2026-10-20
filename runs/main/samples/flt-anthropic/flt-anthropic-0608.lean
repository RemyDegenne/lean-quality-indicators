namespace P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane Filter Function

open scoped MatrixGroups Topology Manifold ModularForm Pointwise

namespace ModularCurve

namespace CuspDecayAux

p2m_open

section Cusp

variable (N : ℕ) [NeZero N] {k : ℤ}

theorem meromorphicAt_F {x : LaurentSeries ℂ} (P : Pres N x) (σ : SL(2, ℤ)) :
    MeromorphicAt (F N x σ) 0 :=
  ((analyticAt_Phi N P.g σ).meromorphicAt.div (analyticAt_Phi N P.h σ).meromorphicAt).congr
    (F_eventuallyEq N P σ).symm

end Cusp
end CuspDecayAux
end ModularCurve
end
end P2MW.S_ModularCurve_exists_isBigO_slash_realize_mul_deriv_realize_of_forall_ordDifferential_nonneg
