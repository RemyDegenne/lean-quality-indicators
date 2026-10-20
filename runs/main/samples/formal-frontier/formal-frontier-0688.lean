@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section CoefficientMaps

open TopRep

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max v w} k G} {Y : TopRep.{max v w} k H}

theorem map_add_apply (φ : H →ₜ* G) (f g : res φ X ⟶ Y) (n : ℕ)
    (x : continuousCohomology n X) :
    (map φ (f + g) n).hom x = (map φ f n).hom x + (map φ g n).hom x := by
  simp only [map_add, TopModuleCat.hom_add, _root_.add_apply]

end CoefficientMaps
end ContinuousCohomology
end
