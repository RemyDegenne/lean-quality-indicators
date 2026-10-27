public section

namespace CFSG.OddStandard.GlueL34

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Preamble

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal (hS : StandardSetting G L) : ¬ L.Normal := by
  have := hS.simple
  intro hN
  have := hN
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal L).elim (ne_bot hS) (ne_top hS)

end Preamble
end CFSG.OddStandard.GlueL34
end
