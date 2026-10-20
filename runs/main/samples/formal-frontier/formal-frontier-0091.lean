@[expose] public section

universe u v w

open CategoryTheory ContRepresentation TopRep

open scoped Topology

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {A B C : TopRep.{max v w} k G}

theorem cochainsMap_resolutionEval (f : A ⟶ B) (n : ℕ)
    (σ : (homogeneousCochains A).X n) (hs : Fin (n + 1) → G) :
    resolutionEval B (n + 1) ((cochainsMap (ContinuousMonoidHom.id G) f).f n σ).1 hs =
      f.hom (resolutionEval A (n + 1) σ.1 hs) := by
  exact resolutionEval_map f (n + 1) σ.1 hs

end ContinuousCohomology
end
