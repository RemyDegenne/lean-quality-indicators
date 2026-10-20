@[expose] public section

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

open CategoryTheory.CartesianMonoidalCategory

open CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

theorem isSeparated_of_grpObj_of_subsingleton [Subsingleton S]
    (G : Over S) [GrpObj G] : IsSeparated G.hom := by
  have : Subsingleton (𝟙_ (Over S)).left := by
    simpa only [Over.tensorUnit_left] using (inferInstance : Subsingleton S)
  exact isSeparated_of_isClosedImmersion_unit G <|
    isClosedImmersion_of_comp_eq_id (toUnit G).left η[G].left (by
      simpa only [Over.tensorUnit_left, Over.toUnit_left, Over.tensorUnit_hom] using Over.w η[G])

end AlgebraicGeometry
end
