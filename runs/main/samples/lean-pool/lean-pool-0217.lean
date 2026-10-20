@[expose] public section

namespace BeyondBethe

open Complexity

theorem matrixEntryLengthSem_processRow
    (rows : List (List ℚ)) (row : List ℚ) (acc : ℕ) :
    (matrixEntryLengthSemStep)^[row.length]
        ⟨rows, row, acc⟩ =
      ⟨rows, [], acc + matrixEntryLengthListCost row⟩ := by
  induction row generalizing acc with
  | nil => simp [matrixEntryLengthListCost]
  | cons q qs ih =>
      rw [List.length_cons, Function.iterate_succ_apply,
        matrixEntryLengthSemStep, ih]
      simp [matrixEntryLengthListCost, Nat.add_assoc]

end BeyondBethe
end
