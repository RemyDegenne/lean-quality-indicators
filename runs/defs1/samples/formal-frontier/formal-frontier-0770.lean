@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped MonObj

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G H N : C} [GrpObj G] [MonObj H] [mN : MonObj N]
  (f : G ⟶ H) (i : N ⟶ G) [IsMonHom f] [IsMonHom i]
  (hPB : IsPullback i (toUnit N) f η[H])

/-- The original kernel projection, regarded as a morphism of group objects. -/
noncomputable def ofIsPullbackHom :
    Grp.mk (grp := ofIsPullback f i hPB) N ⟶ Grp.mk G := by
  -- Retain the witness for the supplied monoid before installing its extension.
  have hi : IsMonHom i := inferInstance
  letI := ofIsPullback f i hPB
  haveI : IsMonHom i := by
    simpa only [ofIsPullback_toMonObj] using hi
  exact Grp.homMk i

end CategoryTheory.GrpObj
end
