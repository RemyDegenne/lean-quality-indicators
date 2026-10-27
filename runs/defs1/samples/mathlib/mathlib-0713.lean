@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/-- A topological space is called an R₀ space, if `Specializes` relation is symmetric.

In other words, given two points `x y : X`,
if every neighborhood of `y` contains `x`, then every neighborhood of `x` contains `y`. -/
@[mk_iff]
class R0Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- In an R₀ space, the `Specializes` relation is symmetric. -/
  specializes_symm : Std.Symm (Specializes : X → X → Prop)

end Separation
end
