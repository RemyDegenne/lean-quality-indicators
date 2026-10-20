public section

variable {ι α β : Type*}

@[inherit_doc] infixl:70 " ⌊/⌋ " => FloorDiv.floorDiv

@[inherit_doc] infixl:70 " ⌈/⌉ " => CeilDiv.ceilDiv

namespace Pi

variable {π : ι → Type*} [AddCommMonoid α] [PartialOrder α]
  [∀ i, AddCommMonoid (π i)] [∀ i, PartialOrder (π i)]
  [∀ i, SMulZeroClass α (π i)]

section FloorDiv

variable [∀ i, FloorDiv α (π i)]

@[push ←]
lemma floorDiv_def (f : ∀ i, π i) (a : α) : f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl

end FloorDiv
end Pi
end
