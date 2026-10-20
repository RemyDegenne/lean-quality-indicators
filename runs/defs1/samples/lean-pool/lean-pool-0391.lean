@[expose] public section

namespace Lean4Itree

/-- The arity (`B`-component) of each interaction-tree node shape: a `ret` node
has no children, a `tau` node has one, and a `vis α e` node has one child per
inhabitant of the response type `α`. -/
def ITree.children {ε : Type u1 → Type v} {ρ : Type u2}
  : ITree.shape ε ρ → Type u1
  | .ret _   => ULift (Fin2 0)
  | .tau     => ULift (Fin2 1)
  | .vis α _ => α

end Lean4Itree
end
