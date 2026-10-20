@[expose] public section

open Set Function TopologicalSpace Topology

variable {α X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace DiscreteQuotient

variable (S : DiscreteQuotient X)

section Comap

variable (g : C(Y, Z)) (f : C(X, Y))

@[simp]
theorem comap_id : S.comap (ContinuousMap.id X) = S := rfl

end Comap
end DiscreteQuotient
end
