set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The map on normalized continuous cohomology induced by a coefficient
morphism for a fixed acting group. -/
noncomputable def normalizedContinuousCohomologyMap
    {X Y : TopRep.{w} k G} (f : X ⟶ Y) (n : ℕ) :
    normalizedContinuousCohomology X n ⟶
      normalizedContinuousCohomology Y n :=
  ContinuousCohomology.map
    (ContinuousMonoidHom.id (ULift.{max v w} G)) (normalizedMap f) n

end TopRep
end
