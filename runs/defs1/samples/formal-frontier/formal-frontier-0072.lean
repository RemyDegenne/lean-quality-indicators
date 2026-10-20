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

/-- A relative norm restricted to the chosen coefficient modules. -/
@[expose] def relativeNorm (S : RestrictedLevelSystem A L)
    (U V : OpenNormalSubgroup G) (h : V ≤ U) :
    S.coefficients V →ₗ[R] S.coefficients U where
  toFun x := ⟨LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h x,
    S.relativeNorm_mem U V h x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

end RestrictedLevelSystem
end ContinuousGroupCohomology.LevelCompact
end
end
