@[expose] public section

namespace WType

variable {α : Type*} {β : α → Type*}

/-- The canonical map to the corresponding sigma type, returning the label of a node as an
  element `a` of `α`, and the children of the node as a function `β a → WType β`. -/
def toSigma : WType β → Σ a : α, β a → WType β
  | ⟨a, f⟩ => ⟨a, f⟩

end WType
end
