public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

open scoped commutatorElement

namespace SBc4

section ThreeSubgroups

variable {G : Type} [Group G]

theorem three_subgroups_mod {X Y Z N : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (N : Set G)) (hY : Y ≤ Subgroup.normalizer (N : Set G))
    (hZ : Z ≤ Subgroup.normalizer (N : Set G)) (h1 : ⁅⁅X, Y⁆, Z⁆ ≤ N) (h2 : ⁅⁅Y, Z⁆, X⁆ ≤ N) :
    ⁅⁅Z, X⁆, Y⁆ ≤ N := by
  set M := Subgroup.normalizer (N : Set G)
  have hN : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (N.subgroupOf M)
  have hmap : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      ⁅⁅A, B⁆, C⁆ = (⁅⁅A.subgroupOf M, B.subgroupOf M⁆, C.subgroupOf M⁆).map M.subtype := by
    intro A B C hA hB hC
    rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
      Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hC]
  have key : ∀ A B C : Subgroup G, A ≤ M → B ≤ M → C ≤ M →
      (⁅⁅A, B⁆, C⁆ ≤ N ↔ ⁅⁅(A.subgroupOf M).map π, (B.subgroupOf M).map π⁆,
        (C.subgroupOf M).map π⁆ = ⊥) := by
    intro A B C hA hB hC
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk', hmap A B C hA hB hC]
    constructor
    · intro h x hx
      exact Subgroup.mem_subgroupOf.mpr (h ⟨x, hx, rfl⟩)
    · rintro h _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (h hx)
  rw [key X Y Z hX hY hZ] at h1
  rw [key Y Z X hY hZ hX] at h2
  rw [key Z X Y hZ hX hY]
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

end ThreeSubgroups
end SBc4
end CFSG.Quasithin
end
