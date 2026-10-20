public section

set_option warningAsError true

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {N G Q : C} [GrpObj G] [GrpObj Q]
  (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q] (e : Q ⟶ G)
  (hN : IsPullback i (toUnit N) q η[Q]) (he : e ≫ q = 𝟙 Q)

include he

/-- The unique kernel component of the section-normalized element. -/
noncomputable def splitKernelRemainder : G ⟶ N :=
  hN.lift ((q ≫ e)⁻¹ * 𝟙 G) (toUnit G)
    (by simpa using normalization_comp q e he (𝟙 G))

end CategoryTheory
end
