public section

open CategoryTheory

namespace TauCeti

namespace ContinuousCohomology

open _root_.ContinuousCohomology

universe u v w

variable (R : Type u) [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (G)

variable {G}

section Res

variable (S : Subgroup G)

variable {R}

/-- Restriction to a subgroup, the first named instance of `ContinuousCohomology.map`. -/
noncomputable def res (X : TopRep R G) (n : ℕ) :
    continuousCohomology n X ⟶
      continuousCohomology n (TopRep.res (S.subtype : S →* G) X) :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

end Res
end ContinuousCohomology
end TauCeti
end
