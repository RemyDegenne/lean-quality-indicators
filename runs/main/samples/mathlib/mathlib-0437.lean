@[expose] public section

namespace Stream'

open Function

universe u v w

namespace WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Computation

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem tail_ofSeq (s : Seq α) : tail (ofSeq s) = ofSeq s.tail := by
  simp only [tail, destruct_ofSeq, map_pure', flatten_pure]
  induction s using Seq.recOn <;> simp only [ofSeq, Seq.tail_nil, Seq.head_nil,
    Option.map_none, Seq.tail_cons, Seq.head_cons, Option.map_some]
  rfl

end WSeq
end Stream'
end
