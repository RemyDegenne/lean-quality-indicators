public section

noncomputable section

open Polynomial ValuativeRel IsLocalRing

open scoped IntermediateField

namespace TauCeti.DyadicSqrtNegOne

@[simp]
theorem inertiaDegree_eq_one : inertiaDegree ℚ_[2] DyadicSqrtNegOne = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _
    isEisensteinAt_X_sq_sub_two_mul_X_add_two _ isRoot_integerOneAddI
    adjoin_one_add_i_eq_top

end TauCeti.DyadicSqrtNegOne
end
end
