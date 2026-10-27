@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v}

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- A set is closed if its complement is open -/
@[wikidata Q320357]
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

end Defs
end
