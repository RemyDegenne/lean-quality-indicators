public section

open scoped commutatorElement

namespace TopologicalAbelianization

section Map

variable {G H K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

@[simp]
theorem map_mk (f : G →* H) (hf : Continuous f) (x : G) :
    map f hf (x : TopologicalAbelianization G) = (f x : TopologicalAbelianization H) :=
  QuotientGroup.map_mk _ _ _ _ x

end Map
end TopologicalAbelianization
end
