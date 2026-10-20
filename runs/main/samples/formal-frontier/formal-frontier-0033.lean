set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v w

open scoped commutatorElement

@[simp]
theorem stableElementaryAbelianizationEquiv_mk (R : Type u) [Ring R] (g : StableGL R) :
    stableElementaryAbelianizationEquiv R
      (QuotientGroup.mk' (stableElementarySubgroup R) g) = Abelianization.of g := by
  exact QuotientGroup.quotientMulEquivOfEq_mk
    (stableElementarySubgroup_eq_commutator R) g

end Matrix.GeneralLinearGroup
end
