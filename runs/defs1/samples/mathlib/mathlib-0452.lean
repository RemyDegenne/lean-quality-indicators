@[expose] public section

open Module Cardinal

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable {L : Type w} [Field L] [Algebra F L]

variable (A B C : IntermediateField F E)

/-- `IntermediateField.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relIndex` but it is `Cardinal` valued. -/
noncomputable def relrank := A.toSubfield.relrank B.toSubfield

end IntermediateField
end
