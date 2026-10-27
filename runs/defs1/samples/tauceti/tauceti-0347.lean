public section

namespace TauCeti.Hodge.StandardWeightOne

open IsBaseChange

open Matrix

open scoped TensorProduct

variable (l : Type*)

/-- The rational vector space `ℚ^{l ⊕ l}` underlying the standard weight-one example. -/
abbrev RationalSpace := l ⊕ l → ℚ

end TauCeti.Hodge.StandardWeightOne
end
