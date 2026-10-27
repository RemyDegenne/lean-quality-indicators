@[expose] public section

open Set

open scoped Computability

universe u v

variable {α : Type u} {σ : Type v} {M : NFA α σ}

namespace NFA

variable (M) in
/-- `M.reverse` constructs an NFA with the same states as `M`, but all the transitions reversed. The
resulting automaton accepts a word `x` if and only if `M` accepts `List.reverse x`. -/
@[simps]
def reverse : NFA α σ where
  step s a := { s' | s ∈ M.step s' a }
  start := M.accept
  accept := M.start

end NFA
end
