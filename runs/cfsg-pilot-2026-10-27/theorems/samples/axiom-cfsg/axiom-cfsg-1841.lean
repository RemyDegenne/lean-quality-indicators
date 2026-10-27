public section

open CFSG.Fischer CFSG.Quasithin.St84.G24DC.Native CFSG.Quasithin.St84.G24DC.Code

open CFSG.LieType.Multipliers.G24 (genArr wordArr toMat)

namespace CFSG.Quasithin.St84.G24Table

theorem getD_map_of_lt {α β : Type*} (f : α → β) (a : Array α) (i : Nat) (d : α) (e : β)
    (hi : i < a.size) : (a.map f).getD i e = f (a.getD i d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

end CFSG.Quasithin.St84.G24Table
end
