@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

namespace FivePathAux

variable {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

variable (M : GModel fivePathGraph)

variable (q : GTup M)

/-- Response at the middle vertex, with the remaining coordinates fixed by `q`. -/
def fC (b : M.L E12) (c : M.L E23) : ℝ := gResp M (2 : Fin 5) (q.1, b, c, q.2.2.2)

end FivePathAux
end TriangleInflation.Graph
end
