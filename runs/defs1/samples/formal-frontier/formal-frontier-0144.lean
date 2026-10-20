@[expose] public section

open CategoryTheory CategoryTheory.Limits TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A B C : TopRep.{max v w} k G}

/-- Preservation of homology by the topology-forgetting functor identifies the
homology of the algebraic complex with the underlying module of the existing
continuous cohomology. -/
noncomputable def moduleCohomologyIso (X : TopRep.{max v w} k G) (n : ℕ) :
    (moduleCochains X).homology n ≅
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology n X) :=
  ((homogeneousCochains X).sc n).mapHomologyIso
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k))

end ContinuousCohomology
end
