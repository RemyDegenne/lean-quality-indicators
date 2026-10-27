@[expose] public section

universe u v

open Set

variable {X : Type u} {Y : Type v}

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toTopology t x` being printed as `{ ofTopology := x }`
by `delabStructureInstance`. -/
@[app_delab WithTopology.toTopology]
meta def WithTopology.delabToTopology : Delab := delabApp

end Notation
end
