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

/-- The published universal-norm submodule, closed in precisely the selected
`L.topology ⊤`, as a closed additive subgroup of total invariants. -/
@[expose] def compactUniversalNormClosedSubgroup :
    ClosedAddSubgroup (group A L (⊤ : OpenSubgroup G)) where
  toAddSubgroup := (universalNormSubmodule A (fullOpenNormalSubgroup G)).toAddSubgroup
  isClosed' := by
    change @IsClosed
      (openSubgroupInvariants A (fullOpenNormalSubgroup G).toOpenSubgroup)
      (L.topology (fullOpenNormalSubgroup G).toOpenSubgroup)
      (universalNormSubmodule A (fullOpenNormalSubgroup G) : Set _)
    exact isClosed_universalNormSubmodule A L (fullOpenNormalSubgroup G)

end ContinuousGroupCohomology.LevelCompact
end
end
