@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

namespace SqWitnessAux

open CycleWitnessAux

section Density

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {t : ℕ}

/-- `f_g(s) = ∏_i (1 + i√q s_{g,i})`, the factor of the family `g`. -/
noncomputable def fam (t : ℕ) (q : ℝ) (s : κ × Fin t → Bool) (g : κ) : ℂ :=
  ∏ i : Fin t, triAtom q (s (g, i))

end Density
end SqWitnessAux
end TriangleInflation.Graph
end
