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

/-- The compatible finite quotient projections from total invariants. -/
@[expose] def compactTateLimitProjection :
    group A L (⊤ : OpenSubgroup G) ⟶ compactZeroTateLimit A L :=
  (compactTotalInvariantsLimitIso A L).inv ≫
    lim.map (compactFiniteTateZeroProjection A L)

end ContinuousGroupCohomology.LevelCompact
end
end
