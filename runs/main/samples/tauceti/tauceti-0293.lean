public section

noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K]

theorem conductor_le_toRingOfIntegers (O : NumberFieldOrder K) :
    (O.conductor : Set (𝓞 K)) ⊆ O.toRingOfIntegers :=
  fun _ hx ↦ O.mem_toRingOfIntegers.mpr (O.conductor_le_order hx)

end NumberFieldOrder
end TauCeti.GlobalNumberFields
end
end
