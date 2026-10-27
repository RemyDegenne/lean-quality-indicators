public section

namespace CFSG.CGT.PushingUpLit.T2KR.Model613

open DihedralGroup

open scoped commutatorElement

namespace Struct613Rel

variable {G : Type} [Group G] {g₀ g₁ g₂ g₃ ξ ρ u β : G}
  (hR : Struct613Rel g₀ g₁ g₂ g₃ ξ ρ u β)

include hR

theorem part_L :
    ⁅S613 g₀ g₁ g₂ g₃ ξ ρ u β, S613 g₀ g₁ g₂ g₃ ξ ρ u β⁆ ≤
      Subgroup.closure ({g₀, g₁, g₂, g₃, ρ, u} : Set G) := by
  rw [← hR.range_Phi, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  rintro _ ⟨t, ht, rfl⟩
  exact hR.Phi_mem_N00 (comm_top_le_N00 ht)

end Struct613Rel
end CFSG.CGT.PushingUpLit.T2KR.Model613
end
