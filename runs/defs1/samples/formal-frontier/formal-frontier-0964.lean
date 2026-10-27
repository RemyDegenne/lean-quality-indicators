public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.CommRingForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)

/-- The inverse natural isomorphism, from underlying ring pullback to
pullback of the underlying sheaf. -/
noncomputable def inverseComparisonIso :
    TopCat.Sheaf.pullback CommRingCat.{v} g ⋙ underlyingSheaf X ≅
      underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g :=
  (canonicalComparisonIso g).symm

end TopCat.Sheaf.CommRingForget
end
