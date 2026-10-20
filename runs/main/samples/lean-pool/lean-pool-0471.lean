@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineRationalVectorSub_done_iterate
    (extra : ℕ) (accumulator payload bound : List Bool) :
    (machineRationalVectorSubStep)^[extra]
      (machineRationalTransposeMulVectorPack [] accumulator payload bound) =
      machineRationalTransposeMulVectorPack [] accumulator payload bound := by
  induction extra with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [machineRationalVectorSubStep]

end BeyondBethe
end
