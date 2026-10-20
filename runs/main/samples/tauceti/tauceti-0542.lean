public section

noncomputable section

open Filter

open scoped NNReal Topology

namespace TauCeti.Semigroups

open TauCeti.Complexification

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace StronglyContinuousSemigroup

theorem HasGrowthBound.complexify {S : StronglyContinuousSemigroup X} {ω M : ℝ}
    (h : S.HasGrowthBound ω M) : S.complexify.HasGrowthBound ω M :=
  (S.hasGrowthBound_complexify_iff ω M).2 h

end StronglyContinuousSemigroup
end TauCeti.Semigroups
end
end
