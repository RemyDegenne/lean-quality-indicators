public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

variable {W : Subgroup G}

omit [Finite G] in
theorem bar_eq_iff {g h : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hh : h ∈ Subgroup.normalizer (W : Set G)) : bar hg = bar hh ↔ g⁻¹ * h ∈ W ⊔ OCW W := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
end
