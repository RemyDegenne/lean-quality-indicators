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

theorem resolutionMap_id_isEmbedding (i : A ⟶ B)
    (hi : Topology.IsEmbedding i.hom) (n : ℕ) :
    Topology.IsEmbedding (resolutionMap (ContinuousMonoidHom.id G) i n).hom := by
  exact ⟨resolutionMap_id_isInducing i hi.isInducing n,
    resolutionMap_injective (ContinuousMonoidHom.id G) i (fun g => ⟨g, rfl⟩)
      hi.injective n⟩

end
end ContinuousCohomology
end
