public section

namespace TauCeti.ContCohomology

open CategoryTheory

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M]

section System

/-- The explicit degree-two transition from the `U`-level to the `V`-level, for `V ≤ U`.

It is defined directly by compatible-pair functoriality from the quotient homomorphism
`G ⧸ V → G ⧸ U` and the inclusion of invariant coefficients `M^U → M^V`. -/
noncomputable def explicitFiniteQuotientTransition2 (U V : OpenNormalSubgroup G) (hVU : V ≤ U) :
    H2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M) →+
      H2 (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M) :=
  explicitMap2 (G ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup M)
    (G ⧸ V.toSubgroup) (FixedPoints.addSubgroup V.toSubgroup M)
    (continuousFiniteQuotientMap G hVU) (fixedPointsInclusion hVU)
    continuous_of_discreteTopology
      (fixedPointsInclusion_continuousFiniteQuotientMap_smul G M hVU)

end System
end TauCeti.ContCohomology
end
