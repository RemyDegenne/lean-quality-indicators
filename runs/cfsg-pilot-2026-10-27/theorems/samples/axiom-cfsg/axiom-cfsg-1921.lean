public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup

open scoped MatrixGroups commutatorElement

theorem sl23_mul_self : ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by
  decide

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
end
