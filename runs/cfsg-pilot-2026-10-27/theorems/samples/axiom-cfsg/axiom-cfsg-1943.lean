public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

variable [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

theorem pCoreOf_sup_uOfL22_le_normalizer_X (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) ≤ Subgroup.normalizer (rconj (wOfU T M) g : Set G) :=
  le_normalizer_rconj_of (mem_normalizer_pCoreOf_sup g hg _)
    (h.pCoreOf_sup_uOfL22_le_normalizer_W hU hg)

end Hyp1281Two
end CFSG.Quasithin
end
