@[expose] public section

open MeasurableSpace Set

open scoped MeasureTheory

variable {α β : Type*}

section UnionInter

variable {α ι : Type*}

theorem piiUnionInter_singleton (π : ι → Set (Set α)) (i : ι) :
    piiUnionInter π {i} = π i ∪ {univ} := by
  ext1 s
  simp only [piiUnionInter, exists_prop, mem_union]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨t, hti, f, hfπ, rfl⟩
    simp only [subset_singleton_iff, Finset.mem_coe] at hti
    by_cases hi : i ∈ t
    · have ht_eq_i : t = {i} := by
        ext1 x
        rw [Finset.mem_singleton]
        exact ⟨fun h => hti x h, fun h => h.symm ▸ hi⟩
      simp only [ht_eq_i, Finset.mem_singleton, iInter_iInter_eq_left]
      exact Or.inl (hfπ i hi)
    · have ht_empty : t = ∅ := by
        ext1 x
        simp only [Finset.notMem_empty, iff_false]
        exact fun hx => hi (hti x hx ▸ hx)
      simp [ht_empty, iInter_univ, Set.mem_singleton univ]
  · rcases h with hs | hs
    · refine ⟨{i}, ?_, fun _ => s, ⟨fun x hx => ?_, ?_⟩⟩
      · rw [Finset.coe_singleton]
      · rw [Finset.mem_singleton] at hx
        rwa [hx]
      · simp only [Finset.mem_singleton, iInter_iInter_eq_left]
    · refine ⟨∅, ?_⟩
      simpa only [Finset.coe_empty, subset_singleton_iff, mem_empty_iff_false, IsEmpty.forall_iff,
        imp_true_iff, Finset.notMem_empty, iInter_false, iInter_univ, true_and,
        exists_const] using! hs

end UnionInter
end
