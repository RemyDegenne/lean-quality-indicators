public section

noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

namespace FiniteOrderInfinityType

variable {K : Type*} [Field K]

/-- A finite-order infinity type as a continuous infinity type: its real signs are retained, and
all modulus exponents and complex angular frequencies are zero. -/
def toContinuous : FiniteOrderInfinityType K →+ ContinuousInfinityType K where
  toFun ε :=
    { realExponent := 0
      realParity := ε
      complexExponent := 0
      complexAngularFrequency := 0 }
  map_zero' := by
    apply ContinuousInfinityType.ext <;> funext w <;> simp
  map_add' _ _ := by
    apply ContinuousInfinityType.ext <;> funext w <;> simp

end FiniteOrderInfinityType
end TauCeti.GlobalNumberFields
end
end
