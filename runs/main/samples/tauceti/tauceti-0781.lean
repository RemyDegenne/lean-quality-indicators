public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntermediateCarrier

variable {L : IntegralLattice V}

@[simp]
theorem index_bot : index (⊥ : L.IntermediateCarrier) = 1 := by
  calc
    index (⊥ : L.IntermediateCarrier) = relIndex ⊥ ⊥ := (relIndex_bot_left ⊥).symm
    _ = 1 := relIndex_self ⊥

end IntermediateCarrier
end IntegralLattice
end TauCeti
end
