@[expose] public section

universe u

namespace BoundedLatticeHom

variable {A : Type u} [Lattice A] [BoundedOrder A]

/-- The order ideal of elements sent to `false` by a Boolean-valued bounded lattice
homomorphism. -/
def falseIdeal (f : BoundedLatticeHom A Bool) : Order.Ideal A where
  carrier := {a | f a = false}
  nonempty' := ⟨⊥, by simp⟩
  directed' := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    change f a = false at ha
    change f b = false at hb
    change f (a ⊔ b) = false
    rw [map_sup, ha, hb]
    rfl
  lower' := by
    intro a b hab hb
    change f a = false at hb
    change f b = false
    exact le_bot_iff.mp (by simpa [hb] using (OrderHomClass.monotone f hab))

end BoundedLatticeHom
end
