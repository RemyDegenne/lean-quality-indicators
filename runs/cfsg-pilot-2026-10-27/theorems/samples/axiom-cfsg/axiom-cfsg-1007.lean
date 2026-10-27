public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem ringCommContained_simpleRoot
    (τ : Tag) (R : Type) [CommRing R] (i : Fin τ.rank)
    (β : Root τ) (hβ : 0 < height β.1) (hne : β ≠ simpleRoot τ i) :
    (rootOperatorFamily τ).RingCommContained R (simpleRoot τ i) β :=
  RootOps.ringCommContained_of_checks R (RootOps.dataChecks τ).valid (RootOps.dataChecks τ).tab
    (RootOps.repsCheck_repsOf τ) (RootOps.coverCheck_coverOf τ) i β hβ hne

end CFSG.LieType.Chevalley
end
