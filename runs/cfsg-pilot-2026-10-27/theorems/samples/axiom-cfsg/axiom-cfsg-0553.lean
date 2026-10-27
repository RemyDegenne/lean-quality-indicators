public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open Subgroup CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert CFSG.LocalAnalysis.ComponentInitial

theorem no_component_of_selfCentralizing {G : Type*} [Group G] [Finite G] {K M : Subgroup G}
    (hMK : M ≤ K) [hMn : (M.subgroupOf K).Normal] (hM : IsPGroup 2 M)
    (hC : K ⊓ Subgroup.centralizer (M : Set G) ≤ M) (B : Subgroup K) :
    ¬ CFSG.IsComponent B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hB
  have hM' : IsPGroup 2 (M.subgroupOf K) :=
    hM.of_equiv (Subgroup.subgroupOfEquivOfLe hMK).symm
  have hBM : B ≤ M.subgroupOf K := by
    rcases CFSG.LocalCores.component_normal_subgroup hB hMn with h | h
    · exact h
    · intro b hb
      refine Subgroup.mem_subgroupOf.2 (hC (Subgroup.mem_inf.2 ⟨b.2, ?_⟩))
      refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hb
      have := Subgroup.mem_centralizer_iff.1 hc ⟨g, hMK hg⟩ (Subgroup.mem_subgroupOf.2 hg)
      exact congrArg Subtype.val this
  exact CFSG.Sporadic.SuzOddCore.not_isComponent_of_le_pgroup hM' hBM hB

end CFSG.Sporadic.Co2Schreier
end
