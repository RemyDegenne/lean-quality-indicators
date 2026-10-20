public section

open AlgebraicGeometry CategoryTheory

open scoped CategoryTheory.MonObj

namespace TauCeti.RankTwoBLieIndex

variable (d : RankTwoBLieIndex)

/-- **The explicit rank-two type-`C` carrier is equivalent to the points of the pinned `Sp₄/ℤ`
group scheme.** -/
noncomputable def carrierEquivPinned : d.AmbientGroup ≃* d.PinnedGroup :=
  d.carrierEquivSymplectic.trans d.pinnedEquivSymplectic.symm

end TauCeti.RankTwoBLieIndex
end
