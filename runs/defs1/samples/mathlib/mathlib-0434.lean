@[expose] public section

open scoped ENNReal

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toLp p x` being printed as `{ ofLp := x }` by `delabStructureInstance`. -/
@[app_delab WithLp.toLp]
meta def WithLp.delabToLp : Delab := delabApp

end Notation
end
