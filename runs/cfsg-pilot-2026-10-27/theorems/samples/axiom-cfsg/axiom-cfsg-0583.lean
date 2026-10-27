public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.RankThree.Classical (subfieldGL subfieldGL_mem_gramSU coe_subfieldGL subfieldGL_injective
  exists_subfieldGL_eq_of_fixed mem_gramSU_of_subfieldGL fixSubfield_unitaryFieldData
  fixSubfield_unitaryFieldData_bar isPerfect_gramSU_one)

open CFSG.LieType.Chevalley (fixSubfield)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Transport

variable {G : Type} [Group G] {I : Subgroup G}

theorem tr_eq_map {H₀ H : Type} [Group H₀] [Group H] {Ψ : ↥I →* H} (ι : H₀ →* H)
    {K Y : Subgroup G} (hKI : K ≤ I) (hYK : Y ≤ K) (ψ' : ↥K → H₀)
    (hψ' : ∀ x : ↥K, Ψ ⟨x, hKI x.2⟩ = ι (ψ' x)) {U T : Subgroup H₀}
    (hsurj : ∀ u ∈ U, ∃ x : ↥K, ψ' x = u) (hTU : T ≤ U)
    (hiff : ∀ x : ↥K, (x : G) ∈ Y ↔ ψ' x ∈ T) : tr I Ψ Y = T.map ι := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxY : (x : G) ∈ Y := hx
    have hxK : (x : G) ∈ K := hYK hxY
    refine ⟨ψ' ⟨x, hxK⟩, (hiff ⟨x, hxK⟩).mp hxY, ?_⟩
    exact (hψ' ⟨x, hxK⟩).symm
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hsurj t (hTU ht)
    refine ⟨⟨x, hKI x.2⟩, ?_, ?_⟩
    · exact (hiff x).mpr (hx ▸ ht)
    · rw [hψ' x, hx]

end Transport
end CFSG.RankThree.PartOne.CTP
end
