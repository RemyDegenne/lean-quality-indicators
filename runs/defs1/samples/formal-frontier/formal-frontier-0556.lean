@[expose] public section

universe uR uM uM' uM'' uN uN' uN'' uI uP uL

namespace BalancedTensorProduct

variable {R : Type uR} [Ring R]

variable {M : Type uM} {M' : Type uM'} {M'' : Type uM''}

variable {N : Type uN} {N' : Type uN'} {N'' : Type uN''}

variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']

variable [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']

variable [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module Rᵐᵒᵖ M'']

variable [Module R N] [Module R N'] [Module R N'']

section Free

variable {ι : Type uI}

/-- A balanced tensor with a free right module, evaluated coordinatewise. -/
noncomputable def freeToFinsupp :
    BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N →+ (ι →₀ N) :=
  lift freeBalancedMap

end Free
end BalancedTensorProduct
end
