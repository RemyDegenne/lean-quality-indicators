namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

lemma selectedBoundaryAt_exists_above {d : ℕ} (ℓ : Vector d)
    (B : Lattice d × Lattice d → Prop) (H : ℝ)
    (hB : ∀ z w, H ≤ dot (realPosition z) ℓ → B (z,w))
    (P : Path d × Path d) (h : ∃ n m, BoundaryAt ℓ H P n m) :
    ∃ n m, selectedBoundaryAt ℓ B P n m := by
  obtain ⟨n,m,hn⟩ := h
  exact selectedBoundaryAt_exists ℓ B P ⟨n,m,hn.1,hn.2.1,hn.2.2.1,hB _ _ hn.2.2.2.1⟩

end DirectionalTransience
end
end
end OAI
