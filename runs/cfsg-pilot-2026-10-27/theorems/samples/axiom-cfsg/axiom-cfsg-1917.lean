public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie

section Levi

theorem e7Embed_xRootE7 : e7Embed xRootE7 = xWeylE8⁻¹ • highRoot .E8 :=
  e7Embed_e8Restrict inv_xWeylE8_smul_highRoot_mem_perpRoots.2

end Levi
end CFSG.SeitzReduction.E8Pilot
end
