@[expose] public section

namespace Utilities

open Multiset Finset

variable {G : CFGraph}

theorem nonempty_relCycle_of_forward_step {V : Type*} [Finite V] {R : V → V → Prop}
    (hirr : ∀ v : V, ¬ R v v) {P : V → Prop} (step : ∀ v, P v → ∃ w, P w ∧ R v w)
    {v₀ : V} (h₀ : P v₀) : Nonempty (RelCycle R) :=
  (nonempty_relCycle_of_backward_step (R := fun u v => R v u) hirr step h₀).map RelCycle.op

end Utilities
end
