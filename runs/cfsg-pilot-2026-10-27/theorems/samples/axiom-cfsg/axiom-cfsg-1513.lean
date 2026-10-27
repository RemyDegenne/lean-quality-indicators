public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Balance

open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp22Rest

open scoped commutatorElement

section Act

variable {Y : Type} [Group Y] [Finite Y]

theorem odd_card_layerO (K' K : Subgroup Y) (c : Y) : Odd (Nat.card ↥(layerO K' K c)) := by
  have hle : (layerO K' K c).map (LayerΓ.toY K' c) ≤ oddCoreIn K := Subgroup.map_comap_le _ _
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (LayerΓ.toY_injective K' c)] at h1
  exact (odd_card_oddCoreIn K).of_dvd_nat h1

end Act
end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
end
