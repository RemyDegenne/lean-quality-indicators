public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open TauCeti.ContCohomology

universe u

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U : Subgroup G) [U.Normal] (M : Type u) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  (hU : IsOpen (U : Set G)) [U.FiniteIndex]

theorem corestriction_comp_res_eq_sum_conjNormalMap (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (t x : G ⧸ U) = x) (n : ℕ) :
    corestriction U M hU n ≫ res U (ofDiscreteModule ℤ G M) n =
      ∑ x, conjNormalMap U M (t x) n :=
  corestriction_comp_res_eq_sum_of_trace_comp_unit U M hU U n _ _
    (trace_comp_unit_eq_sum_conjCoind U M t ht) fun x => shapiroMap_comp_conjNormalMap U M (t x) n

end TauCeti.ContinuousCohomology
end
