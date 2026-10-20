public section

noncomputable section

open NumberField

open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- The monoid of nonzero ideals of an order coprime to its conductor. The order is represented
by its copy `O.toRingOfIntegers` inside `𝓞 K`, and the conductor by its contraction to it. -/
def integralIdealsAwayConductor : Submonoid (Ideal O.toRingOfIntegers) where
  carrier := {I | I ≠ ⊥ ∧
    I ⊔ O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) = ⊤}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {I J} hI hJ := ⟨mul_ne_zero hI.1 hJ.1, Ideal.isCoprime_iff_sup_eq.mp <|
    (Ideal.isCoprime_iff_sup_eq.mpr hI.2).mul_left (Ideal.isCoprime_iff_sup_eq.mpr hJ.2)⟩

end NumberFieldOrder
end TauCeti.GlobalNumberFields
end
end
