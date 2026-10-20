@[expose] public section

open CategoryTheory Filter

open scoped Topology

universe u

/-- A presentation of a topological group as a cofiltered limit of finite groups. -/
structure FiniteGroupPresentation (G : Type u) [Group G] [TopologicalSpace G] where
  index : Type u
  [smallCategory : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ FiniteGrp.{u}
  equiv : G ≃ₜ* (ProfiniteGrp.limitCone
    (diagram ⋙ forget₂ FiniteGrp ProfiniteGrp)).pt

end
