public section

namespace TauCeti.ContCohomology

universe u v

section DegreeTwo

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {A : Type v} [AddCommGroup A] [DistribMulAction U A]

theorem homogeneous2_coe_apply_one (f : G × G → DiscreteCoind G U A) (u : U) (h₁ h₂ : G) :
    (homogeneous2 f (u : G) h₁ h₂ : DiscreteCoind G U A) 1 =
      u • f ((u : G)⁻¹ * h₁, h₁⁻¹ * h₂) 1 := by
  simp [homogeneous2_apply, DiscreteCoind.coe_smul]

end DegreeTwo
end TauCeti.ContCohomology
end
