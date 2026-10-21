namespace OAI

namespace MatchingFPRAS.ExecutableSource

open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma probePart_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ i j,0≤w i j) (K D : ℕ)
    (e : Transport.BagEdge (RationalSource.bags w K)) :
    probePart (((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D),sourceKey e)=
      TreeFraction.repr (RationalSource.probePortion w K D e) := by
  unfold probePart isCentral
  dsimp only
  simp only [decide_eq_true_eq,RationalSource.probePortion]
  simp only [mem_centralKeys hn w hw K]
  split_ifs
  · have hD : ((D,1) : Fraction)=TreeFraction.repr (D:ℚ) := by simp [TreeFraction.repr]
    rw [hD]
    exact div_repr (by decide : (0:ℚ)≤1) (Nat.cast_nonneg D)
  · rfl

end MatchingFPRAS.ExecutableSource
end OAI
