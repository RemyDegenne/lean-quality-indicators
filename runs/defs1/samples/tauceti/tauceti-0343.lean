public section

open AlgebraicGeometry CategoryTheory

open scoped CategoryTheory.MonObj

namespace TauCeti.RankTwoBLieIndex

variable (d : RankTwoBLieIndex)

/-- The positive simple-root subgroup of the standard symplectic matrix group at the
Bourbaki-numbered node `i` of `B₂`. -/
noncomputable def symplecticSimpleRootSubgroup (i : Fin d.1.rank) :
    Multiplicative d.1.Closure →* d.StandardGroup :=
  (d.symplecticRootIndex i).hom

end TauCeti.RankTwoBLieIndex
end
