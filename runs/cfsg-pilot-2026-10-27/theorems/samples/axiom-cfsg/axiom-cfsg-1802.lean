namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace Proofs

open Subgroup Pointwise CFSG.FeitThompson

universe u

variable {X : Type*} [Group X] [Finite X]

variable {G : Type*} [Group G] [Finite G]

variable {M : Subgroup G}

theorem localTypes_unique (hsolv : Group.IsSolvable ↥M) {i j : Fin 5}
    (hi : localTypes M i) (hj : localTypes M j) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp only [localTypes_zero, localTypes_one, localTypes_two, localTypes_three,
      localTypes_four] at hi hj <;> first
    | rfl
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inl hi))
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inl hi)))
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inl hi))))
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inr hi))))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inl hj))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inl hj)))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inl hj))))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inr hj))))
    | exact absurd hj (not_isTypeIII_of_isTypeII hsolv hi)
    | exact absurd hj (not_isTypeIV_of_isTypeII hsolv hi)
    | exact absurd hj (not_isTypeV_of_isTypeII hsolv hi)
    | exact absurd hi (not_isTypeIII_of_isTypeII hsolv hj)
    | exact absurd hi (not_isTypeIV_of_isTypeII hsolv hj)
    | exact absurd hi (not_isTypeV_of_isTypeII hsolv hj)
    | exact absurd hj (not_isTypeIV_of_isTypeIII hsolv hi)
    | exact absurd hj (not_isTypeV_of_isTypeIII hsolv hi)
    | exact absurd hi (not_isTypeIV_of_isTypeIII hsolv hj)
    | exact absurd hi (not_isTypeV_of_isTypeIII hsolv hj)
    | exact absurd hj (not_isTypeV_of_isTypeIV hsolv hi)
    | exact absurd hi (not_isTypeV_of_isTypeIV hsolv hj)

end Proofs
end
end CFSG.FeitThompson
