@[expose] public section

open Set Function Topology TopologicalSpace

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section connectedComponentSetoid

namespace ConnectedComponents

theorem isQuotientMap_coe : IsQuotientMap (mk : α → ConnectedComponents α) :=
  isQuotientMap_quot_mk

end ConnectedComponents
end connectedComponentSetoid
end
