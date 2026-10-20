@[expose] public section

open CategoryTheory TopRep

open scoped ZeroObject

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

variable [TopologicalSpace G] [IsTopologicalGroup G]

section ObjectEquations

variable [LocallyCompactSpace G] [DiscreteTopology B] [DiscreteTopology C]
  [TopRep.JointlyContinuous B]

variable (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
  (hp : Function.Surjective p.hom)

@[simp] theorem initialInvariantsSequence_obj_cohomologyB :
    (initialInvariantsSequence i p hi hexact hp).obj 5 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology 1 B) := rfl

end ObjectEquations
end ContinuousCohomology
end
