public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem factZ3RootSp4Two (hK : Nat.card K = 2) : FactZ3RootSp4Two K :=
  fun _ hy => exists_isSpRootSL2_mem_of_orderOf_eq_three hK hy

end CFSG.SeitzReduction.F4Pilot
end
