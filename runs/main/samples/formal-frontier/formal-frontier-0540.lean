@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[simp] theorem coefficientFunctor_map (n : ℕ) {X Y : TopRep.{max v w} k G}
    (f : X ⟶ Y) :
    (coefficientFunctor (k := k) (G := G) n).map f =
      map (ContinuousMonoidHom.id G) f n := rfl

end ContinuousCohomology
end
