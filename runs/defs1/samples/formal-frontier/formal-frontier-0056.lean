public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The compact Hausdorff degree-zero Tate inverse limit. -/
abbrev compactZeroTateLimit : CompHausAddCommGrp.{u} :=
  limit (compactFiniteZeroDeflationDiagram A L)

end ContinuousGroupCohomology.LevelCompact
end
end
