public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4

open scoped commutatorElement

section WBar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem WBar_eq_map_O22Res (z : G) : WBar z = (O22Res ↥(Cen z)).map (toBar z) := by
  unfold WBar barOf
  have h : (WC z).subgroupOf (Cen z) = O22Res ↥(Cen z) :=
    Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective _
  rw [h]

end WBar
end CFSG.GH74.GLS.Stage2.Final.L26
end
