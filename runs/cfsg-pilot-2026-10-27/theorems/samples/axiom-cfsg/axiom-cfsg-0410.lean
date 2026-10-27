public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight

open scoped commutatorElement

namespace M12Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem not_uniqueCoset
    [CaseIAmbient T] (h39 : Lemma39FStar) (cfg : M12Cfg K z J zJ H S)
    (hm1 : sigmaNorm K ≤ Subgroup.normalizer (firstFactor K : Set T)) : ¬ UniqueCosetZ K z :=
  fun hU => cfg.toFrameCfg.endgame_fstar h39 hU fun _ hne hc => cfg.prod_unique hm1 hU hne hc

end M12Cfg
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
end
