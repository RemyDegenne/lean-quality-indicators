namespace OAI

open scoped Classical

open scoped Classical

namespace ArtinCAT0

namespace RayIndex

lemma edge_chain_equal {K : ℕ} (p : Fin (K+1) → Point)
    (hp : (∀ i, 0<(p i).1+(p i).2) ∨ (∀ i, (p i).1<0) ∨ (∀ i, (p i).2≤0)) :
    (∑ j : Fin K, edge (p j.castSucc) (p j.succ)) = edge (p 0) (p (Fin.last K)) := by
  rcases hp with h|h|h
  · rw [edge_chain_diagonal p h,edge_diagonal (h 0) (h (Fin.last K))]
  · rw [edge_chain_left p h,edge_left (h 0) (h (Fin.last K))]
  · rw [edge_chain_low p h,edge_low (h 0) (h (Fin.last K))]

end RayIndex
end ArtinCAT0
end OAI
