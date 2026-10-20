@[expose] public section

open Fintype Function

universe u v

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V) {n : ℕ}

variable {G}

variable {ι α β : Type*} (C : G.Coloring α)

/-- The coloring of an empty graph. -/
def Coloring.ofIsEmpty [IsEmpty V] : G.Coloring α := .mk isEmptyElim fun {v} => isEmptyElim v

end SimpleGraph
end
