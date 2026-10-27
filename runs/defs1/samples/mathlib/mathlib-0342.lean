@[expose] public section

namespace SimpleGraph

variable {α : Type*} {G G' : SimpleGraph α}

section diam

/--
The diameter is the greatest distance between any two vertices, with the value `0` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat

end diam
end SimpleGraph
end
