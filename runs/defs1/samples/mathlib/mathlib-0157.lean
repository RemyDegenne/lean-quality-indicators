public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section T25

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class T25Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Given two distinct points in a T₂.₅ space, their filters of closed neighborhoods are
  disjoint. -/
  t2_5 : ∀ ⦃x y : X⦄, x ≠ y → Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)

end T25
end
