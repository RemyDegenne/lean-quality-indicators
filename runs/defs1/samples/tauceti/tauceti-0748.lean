public section

open AlgebraicGeometry CategoryTheory

open scoped CategoryTheory.MonObj

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

/-- The special isogeny on the pinned symplectic scheme points. -/
noncomputable def pinnedHalfFrobenius :
    d.toRankTwoBLieIndex.PinnedGroup →* d.toRankTwoBLieIndex.PinnedGroup :=
  d.toRankTwoBLieIndex.pinnedEquivSymplectic.symm.toMonoidHom.comp
    ((TauCeti.specialIsogeny (R := d.1.Closure)).comp
      d.toRankTwoBLieIndex.pinnedEquivSymplectic.toMonoidHom)

end TauCeti.SuzukiLieIndex
end
