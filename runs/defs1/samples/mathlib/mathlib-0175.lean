@[expose] public section

namespace SimpleGraph

open Walk

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

variable {G G'}

/-- The unique two-coloring of a forest that colors the given vertices with zero -/
noncomputable def IsAcyclic.coloringTwoOfVerts (hG : G.IsAcyclic) (verts : G.ConnectedComponent → V)
    (h : ∀ C, verts C ∈ C) : G.Coloring (Fin 2) where
  toFun v :=
    let u := verts <| G.connectedComponentMk v
    ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩
  map_rel' := by
    intro u v hadj
    have := ConnectedComponent.sound hadj.reachable
    have := hG.dist_eq_dist_add_one_of_adj_of_reachable _ hadj <| ConnectedComponent.exact <| h _
    grind [top_adj]

end SimpleGraph
end
