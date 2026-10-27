public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix CFSG.Open CFSG.Fischer CFSG.Fischer.Classification.Beta U42F431

open CFSG.ComponentClassification.CatFactsSmall.PSp43

open scoped Pointwise

local instance (priority := high) mkDecEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

theorem mk_pow4 : ∀ t : F4, t ^ 4 = t := by decide +kernel

end CFSG.Quasithin.SimsF5
end
