public section

noncomputable section

open Metric Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

variable [Fintype ι] [Nonempty ι]

/-- The realization of the boundary of the standard one-simplex is homeomorphic to the unit
zero-sphere. By `simplexBoundary_univ_fin_two`, the underlying precomplex of the source is exactly
the boundary of the simplex on the two vertices. -/
noncomputable def realizationOneSimplexBoundaryHomeomorphSphereZero :
    Realization (⊥ : AbstractSimplicialComplex (Fin 2)) ≃ₜ sphere (0 : ℝ) 1 :=
  (realizationBotHomeomorph (ι := Fin 2)).trans finTwoHomeomorphSphereZero

end AbstractSimplicialComplex
end
end
