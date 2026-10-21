namespace OAI

section

noncomputable section

namespace Paper170

open Paper170Geometry

theorem cycle_pairing {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    (G : Graph Vertex Edge) (N : NormalizedDrawing G) (O : SpokeOrders N)
    (z z' : Edge → ℝ) (hz : ∀v, boundary G z v = 0) (hz' : ∀v, boundary G z' v = 0) :
    edgePairing (cycleIntersection O) z z' = 0 := by
  obtain ⟨V⟩ := normalized_vertexTruncation N
  obtain ⟨C,hC⟩ := exists_truncatedSpokeCoordinates_compatible N V O
  exact cycle_pairing_of_coordinates N O V C hC z z' hz hz'

end Paper170
end
end
end OAI
