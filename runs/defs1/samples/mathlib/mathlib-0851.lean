@[expose] public section

open Finset

open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

namespace TopEdgeLabeling

/-- Compose an edge-labeling, by an injection into the vertex type. This must be an injection, else
we don't know how to color `x ~ y` in the case `f x = f y`.
-/
abbrev pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) : TopEdgeLabeling V' K :=
  EdgeLabeling.pullback C ⟨f, by simp⟩

end TopEdgeLabeling
end SimpleGraph
end
