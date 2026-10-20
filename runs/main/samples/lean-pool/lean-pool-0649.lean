@[expose] public section

namespace LeanPool.Erdos132ConvexK3

theorem row4_DD_realization_min_degree_le_six
    {n : ℕ} {P : Fin n → Point ℝ} {d₁ d₂ d₃ : ℝ}
    (G : Row4DDWordRealization P d₁ d₂ d₃) :
    min (vertexDegree P d₁ d₂ d₃ G.first.vertex)
      (vertexDegree P d₁ d₂ d₃ G.second.vertex) ≤ 6 := by
  let firstPackage := fourEdgeEndpointPackage G.pointsInjective G.classes G.first
  let secondPackage := fourEdgeEndpointPackage G.pointsInjective G.classes G.second
  by_cases hlong : 2 * Real.sqrt d₂ ≤ Real.sqrt d₁ + Real.sqrt d₃
  · apply four_edge_cage_long_min_degree_le_six
      (firstPackage.longBound hlong) (secondPackage.longBound hlong)
    intro hstates
    rcases hstates with ⟨hFirstLeft, hFirstRight, hSecondLeft, hSecondRight⟩
    apply fourEdge_two_d1d1_impossible G
    · simpa [hFirstLeft, RealizesCageBand] using firstPackage.leftSpec
    · simpa [hFirstRight, RealizesCageBand] using firstPackage.rightSpec
    · simpa [hSecondLeft, RealizesCageBand] using secondPackage.leftSpec
    · simpa [hSecondRight, RealizesCageBand] using secondPackage.rightSpec
  · apply four_edge_cage_short_min_degree_le_six
      firstPackage.generalBound secondPackage.generalBound
    · intro hstates
      exact fourEdge_mixed_d1_d2_impossible G G.first G.firstSide
        (by simpa [hstates.1, RealizesCageBand] using firstPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using firstPackage.rightSpec)
    · intro hstates
      exact fourEdge_mixed_d2_d1_impossible G G.first G.firstSide
        (by simpa [hstates.1, RealizesCageBand] using firstPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using firstPackage.rightSpec)
    · intro hstates
      exact fourEdge_mixed_d1_d2_impossible G G.second G.secondSide
        (by simpa [hstates.1, RealizesCageBand] using secondPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using secondPackage.rightSpec)
    · intro hstates
      exact fourEdge_mixed_d2_d1_impossible G G.second G.secondSide
        (by simpa [hstates.1, RealizesCageBand] using secondPackage.leftSpec)
        (by simpa [hstates.2, RealizesCageBand] using secondPackage.rightSpec)
    · intro hstates
      rcases hstates with ⟨hFirstLeft, hFirstRight, hSecondLeft, hSecondRight⟩
      apply fourEdge_two_d1d1_impossible G
      · simpa [hFirstLeft, RealizesCageBand] using firstPackage.leftSpec
      · simpa [hFirstRight, RealizesCageBand] using firstPackage.rightSpec
      · simpa [hSecondLeft, RealizesCageBand] using secondPackage.leftSpec
      · simpa [hSecondRight, RealizesCageBand] using secondPackage.rightSpec

end LeanPool.Erdos132ConvexK3
end
