set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

omit [IsTopologicalGroup G] in
lemma crossedMap_id : crossedMap (𝟙 A) = ContinuousLinearMap.id k _ := by
  ext f g
  rfl

end ContinuousCohomology
end
