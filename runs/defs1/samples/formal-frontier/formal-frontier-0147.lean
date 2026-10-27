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

/-- The intersection of the ranges of the actual finite coinvariant norms. -/
@[expose] def compactUniversalNormSet : Set (group A L (⊤ : OpenSubgroup G)) :=
  {x | ∀ S : OpenNormalSubgroup G,
    x ∈ Set.range (normFromFiniteCoinvariants A L S)}

end ContinuousGroupCohomology.LevelCompact
end
end
