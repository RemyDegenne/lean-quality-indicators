public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

local instance : Nonempty (OpenNormalSubgroup G) := ⟨fullOpenNormalSubgroup G⟩

local instance : IsConnected (OpenNormalSubgroup G) :=
  IsCofiltered.isConnected (OpenNormalSubgroup G)

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

/-- Inclusion of the degree-`-1` Tate limit in the coinvariant limit. -/
@[expose] def compactTateLimitInclusion :
    compactNegativeOneTateLimit A L ⟶ compactFiniteCoinvariantsLimit A L :=
  lim.map (compactFiniteTateNegOneInclusion A L)

end ContinuousGroupCohomology.LevelCompact
end
end
