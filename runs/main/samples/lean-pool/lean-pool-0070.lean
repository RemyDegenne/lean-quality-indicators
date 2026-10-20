@[expose] public section

namespace BeyondBethe

open Complexity

theorem list_length_le_binaryListCode_length {α : Type*}
    (encode : α → List Bool) : ∀ xs : List α,
    xs.length ≤ (binaryListCode encode xs).length := by
  intro xs
  induction xs with
  | nil => simp [binaryListCode]
  | cons x xs ih =>
      simp only [List.length_cons, binaryListCode, pair_length]
      omega

end BeyondBethe
end
