public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.normalizer_tP_le (hd : d.Hyp) :
    normalizer (d.tP : Set G) ≤ normalizer (d.B₂ : Set G) := by
  intro n hn
  set φ : G →* G := (MulAut.conj n).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.conj n).injective
  have hZ : d.ZtP.map φ = d.ZtP :=
    map_conj_eq_of_mem_normalizer (d.normalizer_tP_le_normalizer_ZtP hn)
  have ht : d.tP.map φ = d.tP := map_conj_eq_of_mem_normalizer hn
  obtain ⟨hZB, hBt, hBe, hBc⟩ := hd.B₂_spec
  have h1 : d.ZtP ≤ d.B₂.map φ := hZ ▸ Subgroup.map_mono hZB
  have h2 : d.B₂.map φ ≤ d.tP := ht ▸ Subgroup.map_mono hBt
  have h3 : ElemAbMod d.ZtP (d.B₂.map φ) := hZ ▸ hBe.map φ
  have h4 : Nat.card (d.B₂.map φ) = 2 * (2 ^ f) ^ 7 := by
    rw [Subgroup.card_map_of_injective hinj, hBc]
  have e := (hd.card_le_of_elemAbMod_ZtP h1 h2 h3).2 h4
  refine mem_normalizer_of_conj_le fun b hb => ?_
  rw [← e]
  exact ⟨b, hb, rfl⟩

end Data
end CFSG.LocalAnalysis.EvenBN.U5
end
