@[expose] public section

universe u v w z

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G] (N : Subgroup G) [N.Normal]

variable (B : TopRep.{w} k G) [JointlyContinuous B]

variable [DiscreteTopology B]

@[simp] theorem quotientCoind₁Iso_inv_apply
    (F : coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))) (t : G) :
    ((quotientCoind₁Iso N B).inv F).1 t =
      B.ρ t (F (QuotientGroup.mk' N t)) := by
  change (quotientCoind₁Backward N B F).1 t = B.ρ t (F (QuotientGroup.mk' N t))
  exact quotientCoind₁Backward_apply N B F t

end TopRep
end
