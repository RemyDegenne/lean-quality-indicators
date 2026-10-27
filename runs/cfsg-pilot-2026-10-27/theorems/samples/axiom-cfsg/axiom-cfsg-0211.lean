public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer

open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X) (y : X)

variable {h y}

theorem secImage_layerIn {L : Subgroup X} (hLG : L ≤ h.secG0 y)
    (hLc : L ≤ centralizer (h.secB0 y : Set X)) :
    h.secImage y (layerIn L) = layerIn (h.secImage y L) := by
  rw [← TwoQuot.map_layerIn_of_le_centralizer (h.secMk y)
    (h.subgroupOf_le_centralizer_ker y hLc), B5a.layerIn_subgroupOf hLG]

end Hyp52
end CFSG.ComponentClassification.GSThmB
end
