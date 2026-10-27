public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Prop126b

section Single

variable {G : Type} [Group G] [Finite G]

theorem primeCoreOf_barX_le {Y U : Subgroup G} (hUY : U ≤ Y) :
    GLAPPrimeCoreOf 3 (barX 3 Y U) ≤ barX 3 Y (GLAPPrimeCoreOf 3 U) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ : ↥Y →* ↥Y ⧸ GLAPPrimeCore 3 ↥Y := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Y) with hψ
  set A : Subgroup ↥Y := U.subgroupOf Y with hA
  have hker : Nat.Coprime 3 (Nat.card ↥(A ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have hmap := glaPPrimeCore_map_subgroupMap Nat.prime_three ψ A hker
  have hiso := glaPPrimeCore_map_iso 3 (Subgroup.subgroupOfEquivOfLe hUY)
  rintro y ⟨x, hx, rfl⟩
  have hx' : x ∈ (GLAPPrimeCore 3 ↥A).map (ψ.subgroupMap A) := by
    rw [hmap]
    exact hx
  obtain ⟨u, hu, hux⟩ := hx'
  have hu' : (Subgroup.subgroupOfEquivOfLe hUY) u ∈ GLAPPrimeCore 3 ↥U := by
    rw [← hiso]
    exact Subgroup.mem_map_of_mem _ hu
  refine ⟨(u : ↥Y), ?_, ?_⟩
  · refine (Subgroup.mem_subgroupOf).2 ?_
    exact ⟨_, hu', rfl⟩
  · rw [← hux]
    rfl

end Single
end Prop126b
end CFSG.LocalAnalysis.GLTheoremB.MovingAround
end
