public section

open Finset

namespace CFSG.LocalAnalysis.WeakClosure81.Five

section Setup

variable {G : Type*} [Group G]

variable {K K₁ N : Subgroup G}

theorem FiveSetup.core (S : FiveSetup K K₁ N) {y : G} (hy : y ∈ K)
    (h : ∀ g ∈ K, g * y * g⁻¹ ∈ K₁) : y ∈ N := by
  have hmem : ∀ x : ↥K, x ∈ (K₁.subgroupOf K).normalCore ↔ ∀ g ∈ K, g * (x : G) * g⁻¹ ∈ K₁ := by
    intro x
    constructor
    · intro hx g hg
      exact hx ⟨g, hg⟩
    · intro hx b
      exact hx b b.2
  set Nc : Subgroup ↥K := (K₁.subgroupOf K).normalCore with hNc
  set B : Subgroup G := Nc.map K.subtype with hB
  have hBK : B ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBsub : B.subgroupOf K = Nc :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective Nc
  have hBnorm : (B.subgroupOf K).Normal := by
    rw [hBsub]
    infer_instance
  have hNK : N ≤ K := S.nle.trans S.le
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp S.normal
  have hNB : N ≤ B := by
    intro n hn
    refine ⟨⟨n, hNK hn⟩, (hmem ⟨n, hNK hn⟩).mpr fun g hg => ?_, rfl⟩
    exact S.nle ((Subgroup.mem_normalizer_iff.mp (hNnorm hg) n).1 hn)
  rcases S.kn1 B hNB hBK hBnorm with hBN | hBK'
  · have hyB : y ∈ B := ⟨⟨y, hy⟩, (hmem ⟨y, hy⟩).mpr h, rfl⟩
    rw [hBN] at hyB
    exact hyB
  · exfalso
    have hK1 : K ≤ K₁ := by
      intro x hx
      have hxB : x ∈ B := hBK' ▸ hx
      obtain ⟨x', hx', rfl⟩ := hxB
      have := (hmem x').mp hx' 1 K.one_mem
      simpa using this
    have h1 := Subgroup.relIndex_eq_one.mpr hK1
    rw [S.index] at h1
    norm_num at h1

end Setup
end CFSG.LocalAnalysis.WeakClosure81.Five
end
