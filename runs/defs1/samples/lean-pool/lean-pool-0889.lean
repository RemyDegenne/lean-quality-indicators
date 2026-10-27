@[expose] public section

namespace BeyondBethe

/-- Exact number of small steps used to evaluate one recursive search call and
return its result without consuming the pre-existing continuation stack. -/
def kuhnSearchSteps {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (fuel : ℕ) → List (Fin n) → Fin n → Finset (Fin n) →
      ColumnMate n → ℕ
  | 0, _remaining, _row, _seen, _mate => 1
  | _fuel + 1, [], _row, _seen, _mate => 1
  | fuel + 1, col :: remaining, row, seen, mate =>
      if col ∈ seen ∨ A row col = 0 then
        1 + kuhnSearchSteps A (fuel + 1) remaining row seen mate
      else
        let seen' := insert col seen
        match mate col with
        | none => 1
        | some oldRow =>
            let mateWithoutOld := Function.update mate col none
            let recursive :=
              kuhnSearch A fuel (List.finRange n) oldRow seen' mateWithoutOld
            let recursiveSteps :=
              kuhnSearchSteps A fuel (List.finRange n) oldRow seen'
                mateWithoutOld
            match recursive.mate? with
            | some _ => 2 + recursiveSteps
            | none => 2 + recursiveSteps +
                kuhnSearchSteps A (fuel + 1) remaining row recursive.seen mate
termination_by fuel remaining _row _seen _mate => (fuel, remaining.length)

end BeyondBethe
end
