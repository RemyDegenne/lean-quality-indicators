public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec57

theorem not_isSolvable_psl2 {F : Type} [Field F] [Finite F] (h : 3 < Nat.card F) :
    ¬ Group.IsSolvable PSL(2, F) := by
  have := psl2_isPerfect_of_card_gt_three F h
  have : Nontrivial PSL(2, F) := ⟨⟨Borel5.weyl F, 1, Borel5.weyl_ne_one⟩⟩
  exact Group.IsPerfect.not_isSolvable _

end Sec57
end CFSG.Walter.W67
end
