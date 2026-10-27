public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

theorem lab2_exists_dewQb_one : ∀ b : Lab2, b ≠ 0 → ∃ m : Lab2, dewQb b m = 1 := by decide

end CFSG.ClassicalInvolution.Q3.Sec13
end
