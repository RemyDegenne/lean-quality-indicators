@[expose] public section

open Polynomial

variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

variable {K L L'}

variable (S : IntermediateField K L)

section ExtendScalars

namespace Subfield

variable {F E E' : Subfield L} (h : F ≤ E) (h' : F ≤ E') {x : L}

@[simp]
theorem extendScalars_toSubfield : (extendScalars h).toSubfield = E := SetLike.coe_injective rfl

end Subfield
end ExtendScalars
end
