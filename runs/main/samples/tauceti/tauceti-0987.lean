@[expose] public section

open CategoryTheory Opposite

open scoped CategoryTheory.MonObj

universe u v

namespace TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R]

theorem pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift
    (H : _root_.CommHopfAlgCat.{u} R) :
    HopfAlgebra.pointsGroupPresheaf H ⋙ GrpCat.uliftFunctor.{u + 1, u} ⋙
        forget GrpCat.{u + 1} =
      HopfAlgebra.pointsPresheaf H ⋙ CategoryTheory.uliftFunctor.{u + 1, u} := by
  rw [GrpCat.uliftFunctor_comp_forget_eq_forget_comp_uliftFunctor]
  rfl

end TauCeti.CommHopfAlgCat
end
