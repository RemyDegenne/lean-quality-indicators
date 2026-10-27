@[expose] public section

namespace Stream'

universe u v w

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
def TerminatedAt (s : Seq α) (n : ℕ) : Prop :=
  s.get? n = none

end Seq
end Stream'
end
