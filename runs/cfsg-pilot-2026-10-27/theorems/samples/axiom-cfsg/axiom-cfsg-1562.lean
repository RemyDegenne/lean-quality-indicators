public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem L_le_MV (h : Hyp1271 G T L V) : L ≤ h.hyp.MV :=
  le_inf Subgroup.le_normalizer (L_le_normalizer h)

end CFSG.Quasithin.H13.S127.Mod
end
