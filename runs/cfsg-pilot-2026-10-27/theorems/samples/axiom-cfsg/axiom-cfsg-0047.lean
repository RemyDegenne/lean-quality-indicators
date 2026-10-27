public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10J_t_notin_Q [Finite G] (hP5 : Asc82FactPockets5) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    t ∉ secQ K1 K2 := by
  obtain ⟨-, -, htnotL, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  intro htQ
  exact htnotL (le_trans (sec10J_Q_le hP5 hb hctx) inf_le_right htQ)

end CFSG.OddStandard.SmallF3.Omega
end
