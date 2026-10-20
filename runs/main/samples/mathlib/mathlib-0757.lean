@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

theorem T0Space.of_open_cover (h : ∀ x, ∃ s : Set X, x ∈ s ∧ IsOpen s ∧ T0Space s) : T0Space X :=
  T0Space.of_cover fun x _ hxy =>
    let ⟨s, hxs, hso, hs⟩ := h x
    ⟨s, hxs, (hxy.mem_open_iff hso).1 hxs, hs⟩

end Separation
end
