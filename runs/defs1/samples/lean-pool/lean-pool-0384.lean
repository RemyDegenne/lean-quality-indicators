@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

variable {V : Type*} [ORingStruc V]

open FirstOrder FirstOrder.Arith

section «lp_section_1»

variable [V ⊧ₘ* 𝐈Sg0]

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seq₀ (X Y : V) : Prop := ext 4 X = 1 ∧ ext 4 Y = 2

end «lp_section_1»
end Arith
end LO
end «lp_nc_section_1»
end
