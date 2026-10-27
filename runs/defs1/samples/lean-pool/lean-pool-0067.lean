@[expose] public section

namespace LeanPool.Erdos132N14

open scoped BigOperators

noncomputable section

/-- The fourteen-point assertion in the first clause of Erdős Problem 132. -/
def Erdos132ForFourteen (P : Configuration (Fin 14)) : Prop :=
  2 ≤ (P.lowMultiplicityDistances Finset.univ 14).card

end
end LeanPool.Erdos132N14
end
