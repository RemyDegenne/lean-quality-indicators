@[expose] public section

noncomputable section

open Module NumberField NumberField.InfinitePlace NumberField.Units

variable (K : Type*) [Field K]

namespace NumberField.Units.dirichletUnitTheorem

open Finset

variable {K}

section NumberField

variable [NumberField K]

/-- The distinguished infinite place. -/
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

end NumberField
end NumberField.Units.dirichletUnitTheorem
end
end
