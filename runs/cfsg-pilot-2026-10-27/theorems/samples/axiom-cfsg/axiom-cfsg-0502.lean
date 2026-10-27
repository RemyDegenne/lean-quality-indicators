public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31 CFSG.CosetTable

section Chain

theorem u33Hom_surjective : Function.Surjective u33Hom := by
  set H := (u33Hom.range).comap (QuotientGroup.mk' (u64.subgroupOf M64)) with hH
  have hgen : Set.range u33G ∪ Set.range v64 ⊆ (H.map M64.subtype : Set _) := by
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨u33M i, ⟨PresentedGroup.of i, ?_⟩, rfl⟩
      rw [u33Hom, PresentedGroup.toGroup.of]
      rfl
    · have hv : v64 i ∈ M64 := u64_le_M64 (Subgroup.subset_closure ⟨i, rfl⟩)
      refine ⟨⟨v64 i, hv⟩, ⟨1, ?_⟩, rfl⟩
      rw [map_one, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  have hle : M64 ≤ H.map M64.subtype := by
    have h1 : Subgroup.closure (Set.range u33G ∪ Set.range v64) ≤ H.map M64.subtype := by
      rw [Subgroup.closure_le]
      exact hgen
    rwa [← M64_eq_closure] at h1
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨y, hy, hyx⟩ := hle x.2
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy

end Chain
end CFSG.Quasithin.KGC31.Ru
end
