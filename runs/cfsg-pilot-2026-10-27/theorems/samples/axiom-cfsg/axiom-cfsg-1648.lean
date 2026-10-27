public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Defs

variable (K : Type) [Field K]

variable {K}

theorem mem_yRadical_iff {g : adjointGroup .E6 K} :
    g ∈ yRadical K ↔ (g : ModGL .E6 K) ∈ rootSpan .E6 K yRadicalRoots :=
  mem_subgroupOf

end Defs
end CFSG.SeitzReduction.E6Pilot
end
