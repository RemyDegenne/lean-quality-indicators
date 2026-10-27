public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

omit [Finite G] in
theorem centralizerModZ_le_Mc (T : Subgroup G) :
    centralizerModZ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun _ h => h.1

end Setting1422
end CFSG.Quasithin
end
