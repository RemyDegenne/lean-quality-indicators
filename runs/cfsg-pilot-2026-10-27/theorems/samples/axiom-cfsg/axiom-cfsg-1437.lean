public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers

open scoped BigOperators Classical

theorem primitive_twice_root_half {m : ℕ} (hm : 0 < m) {root : ℂ}
    (hroot : IsPrimitiveRoot root (2 * m)) : root ^ m = -1 := by
  have h := hroot.pow (by omega) (show 2 * m = m * 2 by omega)
  exact h.eq_neg_one_of_two_right

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
end
