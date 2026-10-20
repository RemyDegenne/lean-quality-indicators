@[expose] public section

open CategoryTheory TopRep

open scoped ZeroObject

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[simp] theorem initialInvariantsSequence_boundary [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 3 4 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (zeroIso C).inv ≫ connecting i p hi hexact hp 0 := rfl

end ContinuousCohomology
end
