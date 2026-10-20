public section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti

section Boundary

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) k M]
  {e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1))} {x : M}

variable {hk : k ≠ 0} {p : ↥((𝓡∂ (n + 1)).boundary M)}
  {he : e ∈ atlas (EuclideanHalfSpace (n + 1)) M}

variable (M) in
theorem isSmoothEmbedding_subtypeVal_boundary (hk : k ≠ 0) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) k
      (Subtype.val : ↥((𝓡∂ (n + 1)).boundary M) → M) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hk)
  exact ⟨isImmersion_subtypeVal_boundary (n := n) (k := k) M hk,
    ((𝓡∂ (n + 1)).isClosed_boundary hk).isClosedEmbedding_subtypeVal.isEmbedding⟩

end Boundary
end TauCeti
end
