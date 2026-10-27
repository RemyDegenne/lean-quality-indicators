public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem L_le_centralizer (c : Cfg1620 M V₀ V U S R H g B) :
    V ⊔ conjSubgroup V g ≤ centralizer (U : Set G) :=
  sup_le c.cex.V_le_centralizer (c.cex.conj_le_centralizer c.g_mem.2)

end Cfg1620
end CFSG.LocalAnalysis.WeakClosure81
end
