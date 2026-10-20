public section

variable {α β : Type*} {G H K : Graph α β} {S S' : Set α} {F F' B : Set β} {e : β} {u v : α}

open Set symmDiff

namespace Graph

section IsBond

/-- A bond of a graph is a minimal nonempty edge-cut; see
[Diestel, *Graph Theory*, Section 1.9][diestel2017]. -/
@[expose]
def IsBond (G : Graph α β) (F : Set β) : Prop := Minimal (fun F ↦ G.IsEdgeCut F ∧ F.Nonempty) F

end IsBond
end Graph
end
