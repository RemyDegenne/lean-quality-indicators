public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap

open scoped commutatorElement

open Out

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

section Main

variable (d : Std20Frame K K' J S R R' W V z t)

include d

theorem frameX_le_N :
    sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (K : Set G) :=
  fun x hx => ((sec20X_le_normalizers_frame d) hx).1

end Main
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
end
