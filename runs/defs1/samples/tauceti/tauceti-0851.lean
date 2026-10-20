public section

namespace TauCeti.ContCohomology

universe u v w

section CohomologyDegree2

variable (G : Type u) [Monoid G] [TopologicalSpace G] [hcontMul : ContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [hcontSmul : ContinuousSMul G M]

/-- The second continuous cohomology group `H²(G, M) = Z²/B²`.

As for `H¹` the denominator is `B²` viewed inside `Z²`, and the hypotheses in force imply
`TauCeti.ContCohomology.B2_le_Z2`, so the subgroup divided out really is the whole of `B²`. The
inherited quotient topology is again not the intended one, and `H²` is used as a bare additive
group. -/
abbrev H2 :=
  let _h := B2_le_Z2 G M
  (Z2 G M) ⧸ ((B2 G M).addSubgroupOf (Z2 G M))

end CohomologyDegree2
end TauCeti.ContCohomology
end
