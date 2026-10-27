public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Aut20

variable {G : Type} [Group G]

theorem subgroupOf_le20 {A B K : Subgroup G} (h : A ≤ B) : A.subgroupOf K ≤ B.subgroupOf K :=
  fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

end Aut20
end CFSG.Quasithin.H13.A6
end
