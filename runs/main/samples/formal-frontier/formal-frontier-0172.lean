@[expose] public section

universe u v w

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

variable {k : Type u} {G H : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep k G} {Y : TopRep k H}

section

variable {A B : TopRep.{max v w} k G}

theorem resolutionMap_id_isInducing (i : A ⟶ B)
    (hi : Topology.IsInducing i.hom) (n : ℕ) :
    Topology.IsInducing (resolutionMap (ContinuousMonoidHom.id G) i n).hom := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change Topology.IsInducing
      (ContinuousMap.comp
        ((resolutionMap (ContinuousMonoidHom.id G) i n).hom :
          C(resolutionX A n, resolutionX B n)) :
        C(G, resolutionX A n) → C(G, resolutionX B n))
    exact ContinuousMap.isInducing_postcomp _ ih

end
end ContinuousCohomology
end
