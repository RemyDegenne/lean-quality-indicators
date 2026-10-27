public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbedding.Norton.MON5_7

theorem typeRow_isA6_M : BMType.TypeRow S8.isA6 .M := by
  obtain ⟨-, hs, hfin⟩ := CFSG.Monster.Generated.generated_rational_group_finite_simple
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have hnc : ∃ a c : CFSG.Monster.Generated.Gmat, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder]
      norm_num)
  exact @BMType.typeRow_of_model S8.isA6 .M CFSG.Monster.Generated.Gmat _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_isA6_gmat (s := k) hk hJ hT

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor
end
