public section

open scoped NumberField

namespace NumberField

section Unramified

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G K] [IsGaloisGroup G ℚ K]
  {F : Type*} [Field F] [NumberField F] [Algebra ℚ F] [Algebra F K] [IsScalarTower ℚ F K]

omit [IsGaloisGroup G ℚ K] [Algebra ℚ F] [IsScalarTower ℚ F K] in
theorem pow_index_eq_one_of_ramificationIdx_eq_one {H : Subgroup G} [H.Normal]
    [IsGaloisGroup H F K] {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hunr : P.ramificationIdx (𝓞 F) = 1) {g : G} (hg : g ∈ P.inertia G) : g ^ H.index = 1 :=
  Subgroup.disjoint_def.mp (disjoint_inertia_of_ramificationIdx_eq_one H P hP hunr)
    (pow_mem hg _) (H.pow_index_mem g)

end Unramified
end NumberField
end
