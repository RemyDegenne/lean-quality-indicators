@[expose] public section

variable {α β : Type*}

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

/-- A `FloorRing` constructor from the `floor` function alone. -/
@[instance_reducible]
def FloorRing.ofFloor (α) [Ring α] [LinearOrder α] [IsOrderedAddMonoid α] (floor : α → ℤ)
    (gc_coe_floor : GaloisConnection (↑) floor) : FloorRing α :=
  { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }

end
