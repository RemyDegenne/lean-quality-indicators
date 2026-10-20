@[expose] public section

universe u v w

open CategoryTheory ContRepresentation TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G]

theorem coind₁Insert_natural {X Y : TopRep.{max v w} k G}
    [DiscreteTopology X] [DiscreteTopology Y] (f : X ⟶ Y) (m : ℕ) :
    coind₁Insert X m ≫
        (cochainsMap (ContinuousMonoidHom.id G)
          ((coind₁Functor k G).map f)).f m =
      (cochainsMap (ContinuousMonoidHom.id G)
        ((coind₁Functor k G).map f)).f (m + 1) ≫ coind₁Insert Y m := by
  ext σ
  apply Subtype.ext
  exact (insertCoind_natural_apply f m σ.1).symm

end ContinuousCohomology
end
