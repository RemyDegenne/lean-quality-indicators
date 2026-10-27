public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open

open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data

open scoped Pointwise commutatorElement

section K

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem nd11k_mem_K0 (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    {x : G} (hx : x ∈ (Pe11 d ⊓ d.s56V : Subgroup G)) : x ∈ K0 d z₀ := by
  obtain ⟨hxPe, hxV⟩ := mem_inf.1 hx
  exact mem_K0_iff.2 ⟨⟨s56_V_le_Q2 d hxV, Pe_le_P h49 hd hxPe⟩, nd11k_V_comm h10 hxV hz.mem_V⟩

end K
end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11
end
