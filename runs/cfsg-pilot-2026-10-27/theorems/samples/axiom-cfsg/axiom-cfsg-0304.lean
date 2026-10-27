public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem stroth47Inv1_holds : Stroth47Inv1 := by
  intro G _ _ F D m hm dD h hSN hnc e hS hrel
  exact stroth_4_7_inv1 F hm dD h hSN hnc e hS hrel

end CFSG.CGT.Stroth77
end
