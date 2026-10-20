@[expose] public section

open Finset Nat

open Fintype (card)

namespace SimpleGraph

variable {α β 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {G H : SimpleGraph α} {ε δ : 𝕜}

variable (G ε)

variable [Fintype α] [DecidableRel G.Adj] [DecidableRel H.Adj]

variable {G ε}

variable [Nonempty α]

theorem FarFromTriangleFree.cliqueFinset_nonempty [DecidableEq α]
    (hG : G.FarFromTriangleFree ε) (hε : 0 < ε) : (G.cliqueFinset 3).Nonempty :=
  nonempty_of_ne_empty <| cliqueFinset_eq_empty_iff.not.2 <| hG.not_cliqueFree hε

end SimpleGraph
end
