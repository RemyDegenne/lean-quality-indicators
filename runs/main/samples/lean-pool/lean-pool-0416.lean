@[expose] public section

open Matrix Filter

open scoped Matrix Topology

namespace BollobasNikiforov

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

noncomputable section

lemma euclid_sq (w : Fin 2 → ℝ) : euclid w ^ 2 = w ⬝ᵥ w :=
  Real.sq_sqrt (euclid_inner_nonneg w)

end
end BollobasNikiforov
end
