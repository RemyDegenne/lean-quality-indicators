@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Feasibility for the cluster-triple LP**: nonnegative weights on the cluster triples, supported
on the triangles of the cluster graph, whose total through any cluster pair is at most the density
capacity of that pair. -/
def IsClusterTripleLP (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    (x : Finset {S : Finset V // S ∈ P.parts} → ℝ) : Prop :=
  (∀ th, 0 ≤ x th) ∧
  (∀ th, x th ≠ 0 → th ∈ (hostGraph G P ep de).cliqueFinset 3) ∧
  (∀ S T : {S : Finset V // S ∈ P.parts}, S ≠ T →
    ∑ th ∈ triplesThrough P S T, x th ≤ clusterPairCap G (S : Finset V) (T : Finset V))

end Nibble.AX1
end
