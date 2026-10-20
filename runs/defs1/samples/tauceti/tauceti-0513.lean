public section

namespace TauCeti.ContCohomology

universe u v

section DegreeTwo

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {A : Type v} [AddCommGroup A] [DistribMulAction U A]

variable (G) (U) (A) [TopologicalSpace A] [DiscreteTopology A]

/-- **The forward Shapiro map on continuous `2`-cocycles**: restrict a continuous `2`-cocycle of
`G` with coefficients in `Coind_U^G A` to `U`, and evaluate its values at `1`. -/
noncomputable def shapiroCocycles2 : Z2 G (DiscreteCoind G U A) →+ Z2 U A :=
  cocyclesMap2 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

end DegreeTwo
end TauCeti.ContCohomology
end
