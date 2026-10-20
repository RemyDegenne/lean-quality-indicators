@[expose] public section

universe v t u

open CategoryTheory Topology Limits

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

namespace GeneratedByTopCat

variable {X} in
/-- Constructor for objects in the category of `X`-generated spaces. -/
abbrev of (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] :
    GeneratedByTopCat.{v} X where
  obj := ↧Y
  property := by assumption

end GeneratedByTopCat
end
