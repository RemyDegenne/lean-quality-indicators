@[expose] public section

universe u v w

namespace Stream'.WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Get the first element of `s` satisfying `p`. -/
def find (p : α → Prop) [DecidablePred p] (s : WSeq α) : Computation (Option α) :=
  head <| filter p s

end Stream'.WSeq
end
