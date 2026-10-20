@[expose] public section

noncomputable section

open Finset Function

variable {α β ι M N O H : Type*}

@[inherit_doc]
infixr:25 " →₀ " => Finsupp

namespace Finsupp

section OfSupportFinite

variable [Zero M]

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.support f).Finite) : α →₀ M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset

end OfSupportFinite
end Finsupp
end
end
