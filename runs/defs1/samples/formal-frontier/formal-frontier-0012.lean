@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The complement of the east pole, first in the ordered east/west open cover. -/
def circleEastPunctured : TopologicalSpace.Opens sphere1 :=
  ⟨{eastPoint}ᶜ, isOpen_compl_singleton⟩

end SphereTopology
end
end
