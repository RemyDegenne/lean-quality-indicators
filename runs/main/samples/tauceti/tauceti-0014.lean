public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

variable {K}

variable (K) in
theorem exists_hasLMFDBIntrinsicLabel : ∃ d r D, HasLMFDBIntrinsicLabel K d r D :=
  ⟨_, _, _, rfl, rfl, rfl⟩

end TauCeti.NumberField
end
