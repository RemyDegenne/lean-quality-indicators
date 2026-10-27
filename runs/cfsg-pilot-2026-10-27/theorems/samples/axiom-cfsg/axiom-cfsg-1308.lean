public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem

open CFSG.LieType.Steinberg.SpinOdd (IsRootVec IsShort isShort_single elt elt_of_isLong
  elt_of_isShort shortElt_eq)

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

attribute [local instance] TorusLift.centerCommGroup

variable {n : ℕ} {K : Type} [Field K]

theorem x_add (γ : Fin n → ℤ) (s t : K) :
    SpinOdd.x n K γ (s + t) = SpinOdd.x n K γ s * SpinOdd.x n K γ t :=
  SpinOdd.elt_add _ _ s t

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
end
