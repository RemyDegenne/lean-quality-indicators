public section

namespace TauCeti.ContCohomology

universe u v

section DegreeOne

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **Inflation in degree one**: the compatible-pair pullback along the quotient homomorphism
`G → G ⧸ N`, with the invariants `M ^ N` as coefficients. -/
noncomputable def explicitInfl1 :
    H1 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H1 G M :=
  explicitMap1 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (Subgroup.quotientMkContinuousMonoidHom N)
    (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
    N.fixedPoints_subtype_quotientMk_smul

end DegreeOne
end TauCeti.ContCohomology
end
