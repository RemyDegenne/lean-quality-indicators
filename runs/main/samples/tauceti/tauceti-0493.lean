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

section ResLE

variable {R} {H S : Subgroup G}

theorem resLE_def (h : H ≤ S) (X : TopRep R G) (n : ℕ) :
    resLE h X n = _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupInclusion h)
      (𝟙 (TopRep.res (H.subtype : H →* G) X)) n :=
  (rfl)

end ResLE
end ContinuousCohomology
end TauCeti
end
