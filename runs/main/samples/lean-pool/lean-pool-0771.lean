@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace PlaneComplex

variable (K : PlaneComplex)

theorem sampledEdgeChain_vertex_original (cuts : ℕ)
    (i : Fin (Fintype.card K.Vertex)) :
    (K.sampledEdgeChain cuts).vertex
      ⟨2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val, by
        change 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val <
          2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) +
            Fintype.card K.Vertex + 1
        omega⟩ = K.position (K.vertexAt i) := by
  classical
  simp only [sampledEdgeChain]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  have hsub : 2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts) + i.val -
      (2 * Fintype.card K.EdgeFace + Fintype.card (K.EdgeSample cuts)) = i.val := by omega
  congr 2
  exact Fin.ext hsub

end PlaneComplex
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
