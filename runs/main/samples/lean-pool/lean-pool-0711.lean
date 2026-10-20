@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

namespace Sound

variable {Γ : PairGraph} {t : ℕ}

section Nesting

theorem empty_fun_eq (f g : ↥(∅ : Finset (GObs Γ t)) → Bool) : f = g :=
  funext fun o => absurd o.2 (Finset.notMem_empty _)

end Nesting
end Sound
end TriangleInflation.Graph
end
