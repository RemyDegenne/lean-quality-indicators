public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem star_self (X H : Subgroup G) : E2.star X H H = ⊤ := by
  rw [E2.star, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

end C11AmS
end CFSG.Quasithin.Vol2.Ch10.SecB
end
