namespace OAI

noncomputable section

open scoped BigOperators ComplexOrder

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

open Matrix

open Set Filter

open scoped Topology

open scoped BigOperators

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

open scoped BigOperators Topology

open Filter Set

open scoped BigOperators Matrix.Norms.L2Operator

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Energy

open Matrix

variable {L q : ℕ}

lemma pairConfiguration_restrict (v w : Vertex L) (x : Configuration L q) :
    pairConfiguration v w (x v) (x w) = restrictConfiguration {v,w} x := by
  funext u
  have hu : u.val = v ∨ u.val = w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using u.property
  dsimp only [pairConfiguration, restrictConfiguration]
  split_ifs with hv
  · rw [hv]
  · rw [hu.resolve_left hv]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Energy
end
end OAI
