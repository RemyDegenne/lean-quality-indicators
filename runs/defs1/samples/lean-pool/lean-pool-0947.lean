@[expose] public section

noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-- A generated predictor-corrector algorithm: the iterate sequence is no longer a
field.  It is obtained recursively from the initial point by applying the canonical
Newton predictor step and the canonical Newton corrector step. -/
structure HSDGeneratedAlgorithm (n : Nat) where
  /-- Number of equality constraints in the LP data. -/
  m : Nat
  /-- Linear-programming data. -/
  P : LPData m n
  /-- Standard assumptions on the LP data. -/
  std : LPStandardAssumptions P
  /-- Initial HSD state. -/
  w0 : HSState n
  /-- Initial tight-neighborhood certificate. -/
  initial_neigh : HSDNeighborhood ytmBetaTight w0

end HSDInteriorPointLP
end
end
