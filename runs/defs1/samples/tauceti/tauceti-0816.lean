public section

namespace Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The elements whose value is cofinal for `H`, as an ideal — a *left* ideal in general,
since `Ideal A` is `Submodule A A` and `CofinalValueFor.mul_left` supplies left absorption.
Over a commutative ring this is the ideal of **Wedhorn, Lemma 7.1**, whose radicality is
`isRadical_cofinalIdeal`. -/
def cofinalIdeal (v : Valuation A Γ₀)
    {H : TauCeti.ConvexSubgroup v.valueGroup}
    (hH : characteristicSubgroup v < H) : Ideal A where
  carrier := {a | CofinalValueFor v H.toSubgroup a}
  zero_mem' := cofinalValueFor_zero v H.toSubgroup
  add_mem' ha hb := CofinalValueFor.add ha hb
  smul_mem' b _ ha := CofinalValueFor.mul_left hH ha b

end Valuation
end
