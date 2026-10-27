public section

open Finset

open Function (Injective)

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph (Fin 3)) [DecidableRel J.Adj]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The coarse prediction of `J.inducedGraphCount3 G` from a partition `P` of the vertices. Each
assignment `φ` of the vertices of `J` to three distinct parts of `P` contributes the volume
`∏ i, #(φ i)` times, for each pair `i < j`, the edge density `d(φ i, φ j)` if `J.Adj i j` and the
nonedge density `1 - d(φ i, φ j)` otherwise. -/
noncomputable def coarseInducedGraphEstimate3 (P : Finpartition (univ : Finset V)) : ℝ :=
  ∑ φ : Fin 3 → P.parts with Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
    ∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      if J.Adj p.1.1 p.1.2 then (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)
      else 1 - (G.edgeDensity (φ p.1.1) (φ p.1.2) : ℝ)

end SimpleGraph
end
