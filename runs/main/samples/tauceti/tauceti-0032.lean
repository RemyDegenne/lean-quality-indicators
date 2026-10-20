public section

noncomputable section

namespace Set

open Metric Filter TauCeti Topology

open scoped NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem IsLipschitzDomainWith.image_affineIsometryEquiv
    {Omega : Set (WithLp 2 (ℝ × E))} {L : ℝ≥0} (h : Omega.IsLipschitzDomainWith L)
    (g : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) :
    (g '' Omega).IsLipschitzDomainWith L := by
  refine ⟨g.toHomeomorph.isOpenMap _ h.1, fun y hy ↦ ?_⟩
  have hfrontier : g '' frontier Omega = frontier (g '' Omega) := by
    exact g.toHomeomorph.image_frontier Omega
  rw [← hfrontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (h.2 x hx).image_affineIsometryEquiv g

end Set
end
end
