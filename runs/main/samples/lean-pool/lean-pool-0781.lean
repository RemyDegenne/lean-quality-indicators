@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

@[simp] theorem swapTwist_zero (j : Γ.Edge → Fin 2) (e : Γ.Edge) : swapTwist j e 0 = j e :=
  Equiv.swap_apply_left 0 (j e)

end TriangleInflation.Graph
end
