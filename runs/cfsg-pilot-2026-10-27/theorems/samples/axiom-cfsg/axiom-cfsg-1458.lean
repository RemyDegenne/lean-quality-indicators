public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec5cn_pow4_of_mul_self {x : G} (h : x * x = 1) : x ^ 4 = 1 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
  calc x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [h2, one_pow]

end CFSG.OddStandard.SmallF3.Omega
end
