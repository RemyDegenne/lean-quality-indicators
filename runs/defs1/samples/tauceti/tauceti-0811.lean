@[expose] public section

open CategoryTheory Opposite

open scoped CategoryTheory.MonObj

universe u v

namespace TauCeti.CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The fppf sheaf of points, regarded as a group object in type-valued sheaves.

This form is canonically the sheafification of the group-valued points presheaf. Since that
presheaf is already an fppf sheaf, its underlying type-valued sheaf is canonically isomorphic to
`HopfAlgebra.pointsFppfSheaf H` after forgetting the group structure. -/
noncomputable def pointsFppfGroupObject (H : _root_.CommHopfAlgCat.{u} R) :
    Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1))) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.obj
    (pointsPresheafGrp H)

end TauCeti.CommHopfAlgCat
end
