public section

noncomputable section

open Set

namespace TauCeti

namespace Complexification

section Module

variable {X : Type*}

/-- The embedding `x ↦ x + i 0` of a real vector space into its complexification. -/
def ofReal [Zero X] (x : X) : Complexification X := ⟨x, 0⟩

end Module
end Complexification
end TauCeti
end
end
