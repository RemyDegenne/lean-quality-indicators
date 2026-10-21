namespace OAI

noncomputable section

open Set Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem CompactCurveArc.subarc_boundary_eq (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v) :
    closure (A.openSubarc u v) \ A.openSubarc u v =
      {A.map ⟨u,hu,huv.le.trans hv⟩,A.map ⟨v,hu.trans huv.le,hv⟩} := by
  apply Subset.antisymm
  · intro x hx
    rcases A.subarc_frontier hu hv huv hx.1 hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr (mem_singleton_iff.mpr h)
  · intro x hx
    rw [A.subarc_closure hu hv huv]
    rcases hx with h | h
    · rw [h]
      refine ⟨⟨⟨u,hu,huv.le.trans hv⟩,⟨le_rfl,huv.le⟩,rfl⟩,?_⟩
      rintro ⟨t,ht,he⟩
      have heq := congrArg Subtype.val (A.embedding.injective he)
      exact (ne_of_gt ht.1) heq
    · have h := mem_singleton_iff.mp h
      rw [h]
      refine ⟨⟨⟨v,hu.trans huv.le,hv⟩,⟨huv.le,le_rfl⟩,rfl⟩,?_⟩
      rintro ⟨t,ht,he⟩
      have heq := congrArg Subtype.val (A.embedding.injective he)
      exact (ne_of_lt ht.2) heq

end ClosedSurfaceR4.FiniteOrderSmoothing
end
end OAI
