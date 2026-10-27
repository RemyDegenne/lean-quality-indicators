public section

open scoped Pointwise

namespace CFSG

open Equiv

lemma TwoSetC2.eq_one_or_eq_neg (x : TwoSetC2) : x = 1 ∨ x = twoSetC2neg := by
  revert x
  decide

end CFSG
end
