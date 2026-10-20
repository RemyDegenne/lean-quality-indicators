@[expose] public section

namespace Stream'

open Function

universe u v w

namespace WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Computation

/-- auxiliary definition of `destruct_join` over weak sequences -/
@[simp]
def destruct_join.aux : Option (WSeq α × WSeq (WSeq α)) → Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (s, S) => (destruct (append s (join S))).think

end WSeq
end Stream'
end
