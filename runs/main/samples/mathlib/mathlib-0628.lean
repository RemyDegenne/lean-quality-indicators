@[expose] public section

open Function Set Filter Topology

variable {X α α' β γ δ M R : Type*}

section LocallyFinite

variable {ι : Type*} [TopologicalSpace X]

@[to_additive ]
theorem LocallyFinite.exists_finset_nhds_mulSupport_subset {U : ι → Set X} [One R] {f : ι → X → R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : ∀ i, mulTSupport (f i) ⊆ U i)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι), ∃ n, n ∈ 𝓝 x ∧ (n ⊆ ⋂ i ∈ is, U i) ∧
      ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is := by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := {i ∈ hnf.toFinset | x ∈ U i}
    let js := {j ∈ hnf.toFinset | x ∉ U j}
    refine
      ⟨is, (n ∩ ⋂ j ∈ js, (mulTSupport (f j))ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
    · exact (biInter_finset_mem js).mpr fun j hj => IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
        (Set.notMem_subset (hso j) (Finset.mem_filter.mp hj).2)
    · exact (biInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (Finset.mem_filter.mp hi).2
    · have hzn : z ∈ n := by
        rw [inter_assoc] at hz
        exact mem_of_mem_inter_left hz
      replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz)
      simp only [js, Finset.mem_filter, Finite.mem_toFinset, mem_ofPred_eq, mem_iInter,
        and_imp] at hz
      suffices (mulSupport fun i => f i z) ⊆ hnf.toFinset by
        refine hnf.toFinset.subset_coe_filter_of_subset_forall _ this fun i hi => ?_
        specialize hz i ⟨z, ⟨hi, hzn⟩⟩
        contrapose hz
        simp [hz, subset_mulTSupport (f i) hi]
      intro i hi
      simp only [Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨z, ⟨hi, hzn⟩⟩

end LocallyFinite
end
