public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.RankThree.PerfectCover CFSG.Blueprint.Multiplier

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_asc82SchurU43 (hGA : CFSG.Open.GriessAllModelsStatement) : Asc82SchurU43 :=
  fg_asc82SchurU43_of_index_two_unique fun hS =>
    fg_hopf_index_two_unique_u43 hGA
      (CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hS)

end CFSG.OddStandard.SmallF3.Omega
end
