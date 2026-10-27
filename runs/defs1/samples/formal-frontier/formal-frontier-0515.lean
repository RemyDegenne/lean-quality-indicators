public section

set_option autoImplicit false

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ ↦ inferInstance⟩

/-- Continuous coefficient maps on the published compact degree-`-1` Tate limit. -/
@[expose] def compactNegativeOneTateLimitFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} :=
  compactFiniteNegativeOneDeflationDiagramFunctor ⋙ lim

end ContinuousGroupCohomology.LevelCompactRep
end
end
