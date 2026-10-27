@[expose] public section

open Function Set

variable {ι : Sort*} {α β γ : Type*}

namespace BooleanSubalgebra

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ] {L M : BooleanSubalgebra α}
  {f : BoundedLatticeHom α β} {s t : Set α} {a b : α}

/-- The preimage of a Boolean subalgebra along a bounded lattice homomorphism. -/
def comap (f : BoundedLatticeHom α β) (L : BooleanSubalgebra β) : BooleanSubalgebra α where
  carrier := f ⁻¹' L
  bot_mem' := by simp
  compl_mem' := by simp [map_compl']
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

end BooleanAlgebra
end BooleanSubalgebra
end
