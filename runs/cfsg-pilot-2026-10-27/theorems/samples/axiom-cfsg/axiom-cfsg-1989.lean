public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

open scoped commutatorElement

section Bridge

variable {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ)

theorem fact12_iff : fr.Fact12 ↔ (GFrame.ofFrame fr).F12 := Iff.rfl

end Bridge
end CFSG.OddStandard.HigherRank.YamadaG23
end
