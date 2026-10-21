namespace OAI

section

namespace Thomason.Construction.DirectedComplex.Cell

universe u

variable {K : DirectedComplex.{u}}

namespace PositiveTable

@[simp] theorem ofCells_table (as : List (Cell K)) (side : Bool) (n : ℕ) :
    (ofCells as).table side n = (as.map (fun A => A.table side n)).sum := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    change A.table side n + (ofCells as).table side n = _
    simpa only [List.map_cons, List.sum_cons] using congrArg (A.table side n + ·) ih

end PositiveTable
end Thomason.Construction.DirectedComplex.Cell
end
end OAI
