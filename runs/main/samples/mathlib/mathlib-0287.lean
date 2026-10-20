@[expose] public section

open Function Set

variable {ι : Sort*} {α β γ : Type*}

namespace BooleanSubalgebra

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ] {L M : BooleanSubalgebra α}
  {f : BoundedLatticeHom α β} {s t : Set α} {a b : α}

@[simp] lemma supClosed (L : BooleanSubalgebra α) : SupClosed (L : Set α) := L.supClosed'

end BooleanAlgebra
end BooleanSubalgebra
end
