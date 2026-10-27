public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

/-- Continuous coefficient maps on the actual compact finite-coinvariant limit. -/
@[expose] def compactFiniteCoinvariantsLimitFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} :=
  compactFiniteCoinvariantsDiagramFunctor ⋙ lim

end ContinuousGroupCohomology.LevelCompactRep
end
end
