@[expose] public section

open CategoryTheory CategoryTheory.Limits TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A B C : TopRep.{max v w} k G}

@[simp]
theorem moduleCochainsSequence_X₂ (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) :
    (moduleCochainsSequence i p hexact).X₂ = moduleCochains B := rfl

end ContinuousCohomology
end
