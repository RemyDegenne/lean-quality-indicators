public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

open CFSG.QuasithinUnique.Bridge Matrix

open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76_F4

open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

variable (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))))

theorem βU_eq_one_iff_V1_F4 (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) (u : ↥(conjClosure S.V3 H)) :
    C.βU_F4 u = 1 ↔ (u : G) ∈ fsuV1 T V := by
  obtain ⟨-, -, -, -, -, -, -, -, hβk, -⟩ := C.hR
  rw [βU_F4, MonoidHom.comp_apply, hβk, hfix, bot_inf_eq, Subgroup.mem_bot, C.ι_coe_F4,
    A6Mod.secMk_eq_one_iff]

end Ctx76_F4
end Setting4
end CFSG.Quasithin.H13.A6
end
