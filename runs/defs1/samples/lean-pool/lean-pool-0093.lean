@[expose] public section

namespace BeyondBethe

open Complexity

/-- Adds one directed objective summand and advances in row-major order, setting the completion
flag after the final entry and fixing completed states. -/
def directedObjectiveSumSemanticStep {m : ℕ}
    (tau : ℚ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (y : Fin (m * m) → ℚ) (p : ℕ)
    (state : DirectedObjectiveSumSemanticState m) :
    DirectedObjectiveSumSemanticState m :=
  if state.done then state
  else
    let nextAcc := state.acc.add
      (rawDirectedBetheObjectiveCoordinate tau A y p
        state.row state.column)
    if hcolumn : state.column = Fin.last m then
      if hrow : state.row = Fin.last m then
        { state with acc := nextAcc, done := true }
      else
        { state with
            row := betheFloorScanNextFin state.row
            column := ⟨0, by omega⟩
            acc := nextAcc }
    else
      { state with
          column := betheFloorScanNextFin state.column
          acc := nextAcc }

end BeyondBethe
end
