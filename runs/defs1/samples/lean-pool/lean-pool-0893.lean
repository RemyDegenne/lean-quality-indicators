@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

namespace CycleModelAux

/-- The sign response of a model at a vertex: `E[sgn O_v | sources]`. -/
def sResp (M : GModel Γ) (v : Γ.V) (x : ∀ e : Γ.Edge, M.L e) : ℝ :=
  2 * M.resp v (fun e => x e.1) - 1

end CycleModelAux
end TriangleInflation.Graph
end
