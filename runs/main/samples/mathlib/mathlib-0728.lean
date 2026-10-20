public section

open Finset

section DirectedOrders

variable {ι : Sort*} {α : Type*} {r : α → α → Prop} [IsTrans α r] {γ : Type*} [Nonempty γ]
  {f : γ → α} [Finite ι]

theorem Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) :
    ∃ z, ∀ i ∈ s, r (f i) (f z) := by
  convert! D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]

end DirectedOrders
end
