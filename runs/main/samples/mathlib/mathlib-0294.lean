@[expose] public section

open Finset

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

variable {G ε}

variable (G)

variable {G}

variable (G)

theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #s * ε ≤ #(G.nonuniformWitnesses ε s t).1 := by
  rw [nonuniformWitnesses, dite_eq_left h]
  exact (not_isUniform_iff.1 h).choose_spec.2.choose_spec.2.1

end SimpleGraph
end
