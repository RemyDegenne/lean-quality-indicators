public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated Subgroup

variable {G : Type} [Group G]

theorem self_mem_centralizer_twoCore (z : G) : z ∈ centralizer (twoCore z : Set G) := by
  rw [mem_centralizer_iff]
  intro q hq
  exact mem_centralizer_singleton_iff.1 (twoCore_le z hq)

end CFSG.Monster.Existence
end
