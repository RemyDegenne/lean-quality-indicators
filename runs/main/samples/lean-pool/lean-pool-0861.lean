@[expose] public section

open Set Schoenflies

open scoped Graph

namespace Schoenflies

variable {γ : Type*}

variable {H K : Graph γ γ} {e x y v e₁ e₂ : γ}

namespace CellStructure

variable (S : CellStructure γ)

variable {S}

variable {S : CellStructure γ} (d : S.SubdivData)

namespace SplitData

variable {S : CellStructure γ} (d : S.SplitData)

variable {d}

variable (d)

theorem finite_ear_edgeSet : E(d.ear).Finite := by
  rw [d.isPathGraph.edgeSet_eq]; exact d.earWalk.finite_toSet

end SplitData
end CellStructure
end Schoenflies
end
