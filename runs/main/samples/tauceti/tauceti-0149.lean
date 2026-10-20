public section

namespace TauCeti

variable {B : Type*} {A : Matrix B B ℤ}

namespace IsFiniteType

theorem exists_chain_of_reachable (h : IsFiniteType A) {u v : B}
    (huv : (diagramGraph A).Reachable u v) :
    ∃ (n : ℕ) (w : ℕ → B), w 0 = u ∧ w n = v ∧
      Set.InjOn w {i | i ≤ n} ∧
      (∀ i, i < n → A (w i) (w (i + 1)) ≠ 0) ∧
      ∀ i j, i + 1 < j → j ≤ n → A (w i) (w j) = 0 := by
  classical
  let p : (diagramGraph A).Path u v := huv.some.toPath
  let q : (diagramGraph A).Walk u v := p
  have hq : q.IsPath := p.isPath
  refine ⟨q.length, q.getVert, ?_, ?_, ?_, ?_, ?_⟩
  · exact q.getVert_zero
  · exact q.getVert_length
  · exact hq.getVert_injOn
  · intro i hi
    exact (h.diagramGraph_adj_iff.mp (q.adj_getVert_succ hi)).2
  · intro i j hij hj
    by_contra hne
    have hne' : q.getVert i ≠ q.getVert j := fun heq ↦ by
      have := hq.getVert_injOn (by omega : i ≤ q.length) hj heq
      omega
    exact h.isAcyclic_diagramGraph.not_adj_getVert_of_add_one_lt hq hij hj
      (h.diagramGraph_adj_iff.mpr ⟨hne', hne⟩)

end IsFiniteType
end TauCeti
end
