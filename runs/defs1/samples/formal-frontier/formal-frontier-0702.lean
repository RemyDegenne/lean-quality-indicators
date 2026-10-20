set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] (N : Subgroup G) [N.Normal]

/-- Functorial quotient invariants for native topological representations. -/
def quotientInvariantsFunctor : TopRep.{w} k G ⥤ TopRep.{w} k (G ⧸ N) where
  obj := quotientInvariants N
  map := quotientInvariantsMap N
  map_id := by
    intro X
    ext x
    apply Subtype.ext
    rfl
  map_comp := by
    intro X Y Z f g
    ext x
    apply Subtype.ext
    rfl

end TopRep
end
