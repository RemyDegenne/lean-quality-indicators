public section

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

open scoped Classical in
theorem exists_rationalSubset_chain (Aplus : Subring A) (T : Finset A) (s u : A)
    (hu : ∀ v ∈ rationalSubset Aplus T s, v.toValuativeRel.vle u s) : ∃ N : ℕ → Finset A,
      N 0 = {u} ∧
      (∀ i, rationalSubset Aplus (N i) s ⊆ spa Aplus) ∧
      Antitone (fun i ↦ rationalSubset Aplus (N i) s) ∧
      (∀ i < T.card, ∃ t ∈ T, N (i + 1) = insert t (N i)) ∧
      rationalSubset Aplus (N T.card) s = rationalSubset Aplus T s := by
  classical
  refine ⟨fun i ↦ insert u ((T.toList.take i).toFinset), by simp,
    fun i ↦ rationalSubset_subset_spa _ _ _, ?_, ?_, ?_⟩
  · exact fun i j hij ↦ rationalSubset_subset_rationalSubset_of_subset Aplus
      (insert_take_toFinset_mono u T.toList hij) s
  · intro i hi
    have hlen : i < T.toList.length := by simpa [Finset.length_toList] using hi
    refine ⟨T.toList[i], Finset.mem_toList.mp (List.getElem_mem hlen), ?_⟩
    -- `change` only unfolds the chosen witness: `N i` is by definition
    -- `insert u ((T.toList.take i).toFinset)`, so this restates the goal up to defeq.
    change insert u (T.toList.take (i + 1)).toFinset
        = insert T.toList[i] (insert u (T.toList.take i).toFinset)
    ext a
    rw [← List.take_concat_get' _ _ hlen]
    simp only [Finset.mem_insert, List.mem_toFinset, List.mem_append, List.mem_singleton]
    tauto
  · -- As above, `change` only unfolds the witness `N T.card` to its definition.
    change rationalSubset Aplus (insert u (T.toList.take T.card).toFinset) s
        = rationalSubset Aplus T s
    rw [← Finset.length_toList, List.take_length, Finset.toList_toFinset]
    exact rationalSubset_insert_of_forall_vle Aplus T s u hu

end TauCeti.ValuationSpectrum
end
