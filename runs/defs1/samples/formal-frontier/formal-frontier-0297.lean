public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Total invariants carry the identity transition at every deflation level. -/
@[expose] noncomputable def compactTotalInvariantsDiagram :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj _ := group A L (⊤ : OpenSubgroup G)
  map _ := 𝟙 _

end ContinuousGroupCohomology.LevelCompact
end
end
