@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

theorem inseparable_iff_eq [T0Space X] {x y : X} : Inseparable x y ↔ x = y :=
  nhds_injective.eq_iff

end Separation
end
