public section

namespace TauCeti.ContCohomology

open DiscreteCoind

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]
  {U : Subgroup G} [U.FiniteIndex] {M : Type v} [AddCommGroup M]
  [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

variable [IsTopologicalGroup G] [CompactSpace G]

theorem indexTwoShortExact_explicitDelta0 (hU : U.index = 2) (hUo : IsOpen (U : Set G))
    (hM : ∀ m : M, 2 • m = 0) (c : H0 G M) :
    (indexTwoShortExact G U M hU hUo hM).explicitDelta0 c =
      (indexTwoConnectingCocycle hU hUo c (hM c) : H1 G M) := by
  exact (indexTwoShortExact G U M hU hUo hM).explicitDelta0_apply c
    (b := single G U M hUo 1 (c : M))
    (by rw [indexTwoShortExact_proj]; exact (trace_single hUo 1 (c : M)).trans (by simp))
    (unit_indicator_eq_smul_single_sub hU hUo hM c)

end TauCeti.ContCohomology
end
