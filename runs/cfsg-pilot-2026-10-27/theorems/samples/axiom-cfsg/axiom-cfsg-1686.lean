public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Cfg

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1d_inf_eq_bot {L L' : Subgroup Y} (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤)
    (hne : L ≠ L') (hc : Subgroup.center ↥L = ⊥) : L ⊓ L' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxc : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (szh1d_comm_of_ne hL hL' hne w.2 hx.2)
  rw [hc, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

end Cfg
end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
end
