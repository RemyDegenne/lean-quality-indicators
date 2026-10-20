@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The second open in the ordered cover: the complement of the south pole. -/
def sphere2SouthPunctured : TopologicalSpace.Opens sphere2 :=
  ⟨{sphere2SouthPoint}ᶜ, isOpen_compl_singleton⟩

end SphereTopology
end
end
