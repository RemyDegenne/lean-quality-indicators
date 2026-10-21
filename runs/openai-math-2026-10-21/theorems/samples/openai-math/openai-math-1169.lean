namespace OAI

noncomputable section

namespace Matching205.Forward

universe u

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (M : G.Subgraph) (hM : M.IsPerfectMatching)

omit [Fintype V] [DecidableRel G.Adj] in
lemma neighbor_adj (v : V) : M.Adj v (neighbor G M hM v).val :=
  (unique_neighbor G M hM v).choose_spec.1

end Matching205.Forward
end
end OAI
