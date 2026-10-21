namespace OAI

namespace ChromaticCyclic

namespace CyclicStep

variable {G : Type*} [Group G]

theorem exists_larger (hnc : NormalizerCondition G) (H : Subgroup G) (hH : H < ⊤) :
    ∃ K, H < K ∧ CyclicStep H K := by
  let N := Subgroup.normalizer (H : Set G)
  have hHN : H < N := hnc H hH
  obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt hHN
  let q := QuotientGroup.mk' (H.subgroupOf N)
  let Z := Subgroup.zpowers (q ⟨x, hxN⟩)
  let K := (Z.comap q).map N.subtype
  have hb : ((⊥ : Subgroup (N ⧸ H.subgroupOf N)).comap q).map N.subtype = H := by
    change (QuotientGroup.mk' (H.subgroupOf N)).ker.map N.subtype = H
    rw [QuotientGroup.ker_mk', Subgroup.map_subgroupOf_eq_of_le hHN.le]
  have hs : CyclicStep H K := by
    rw [← hb]
    exact ((CyclicStep.bot Z).comap q).map N.subtype
  have hxK : x ∈ K := by
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, Subgroup.mem_zpowers _, rfl⟩
  refine ⟨K, lt_of_le_of_ne hs.le ?_, hs⟩
  intro he
  exact hxH (he.symm ▸ hxK)

end CyclicStep
end ChromaticCyclic
end OAI
