public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι)

variable [DecidableEq ι]

variable (v : ι)

/-- The punctured geometric closed star, expressed by the apex coordinate being less than one. -/
def puncturedClosedStar : Set (Realization K) :=
  {x | x ∈ closedStarRealization K {v} ∧ x.1 v < 1}

end AbstractSimplicialComplex
end
end
