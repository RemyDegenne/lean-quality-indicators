public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace RestrictedLevelSystem

variable {A : Rep.{u} R G} {L : LevelCompact A}

open CategoryTheory

/-- The compact Hausdorff additive group carried by a restricted coefficient
module at one open normal level. Its carrier and inherited topology are exposed
so ordinary importing modules can construct continuous maps on the chosen
coefficient subtype. -/
@[expose] noncomputable def group (S : RestrictedLevelSystem A L)
    (U : OpenNormalSubgroup G) : CompHausAddCommGrp.{u} := by
  let _ : TopologicalSpace (S.coefficients U) := S.topology U
  let _ : T2Space (S.coefficients U) := S.t2 U
  let _ : CompactSpace (S.coefficients U) := S.compact U
  let _ : IsTopologicalAddGroup (S.coefficients U) := S.topologicalAddGroup U
  exact CompHausAddCommGrp.of (S.coefficients U)

end RestrictedLevelSystem
end ContinuousGroupCohomology.LevelCompact
end
end
