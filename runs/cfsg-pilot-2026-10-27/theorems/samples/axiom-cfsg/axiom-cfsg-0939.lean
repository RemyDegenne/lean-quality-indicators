public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

open scoped commutatorElement

section Hl1

variable {G : Type} [Group G] [Finite G]

theorem CxK_le_centralizer {x : G} {K : Subgroup G} (hK : IsQuasisimple ↥K) :
    CxK x K ≤ centralizer (K : Set G) := fun _ hc =>
  Subgroup.mem_centralizer_iff.2 fun k hk => (GLS.Th2.commute_of_mem_cSec hK hc.2 k hk).symm

end Hl1
end CFSG.GH74.Generic.BProg
end
