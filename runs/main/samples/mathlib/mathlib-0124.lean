@[expose] public section

open Set Filter Function Topology

variable {X Y Z α ι : Type*} {A : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [∀ i, TopologicalSpace (A i)] {x y z : X} {s : Set X} {f g : X → Y}

attribute [local instance] specializationPreorder

local infixl:0 " ~ᵢ " => Inseparable

theorem Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x := h.ge

end
