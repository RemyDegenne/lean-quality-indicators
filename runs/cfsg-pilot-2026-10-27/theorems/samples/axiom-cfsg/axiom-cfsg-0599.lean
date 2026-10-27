public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie

open CFSG.Assembly.LowTwoRank

open CFSG.Quasithin (perfectCore)

open scoped MatrixGroups

local instance f4PilotMainPieceTablesNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Assembly

theorem neighbourPieceCards_swap_of_input (hS : SwapNeighbourInput) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : L ≃* adjointGroup .F4 K} {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    {N : AmalgamNeighbour} (hN : N ≠ .X') (h : HR8Kind e t f N .swap) :
    neighbourPieceCards e N = pieceOrders .swap (2 ^ f) := by
  obtain ⟨Kc, hc, hd, hE, hfix⟩ := hS G L K e t f hw hf N hN h
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨Φ⟩ := nonempty_swapNeighbourIso N htt hc hd hE hfix
  rw [neighbourPieceCards_of_swapNeighbourIso Φ hN (hw.card_eq ▸ four_le_two_pow_of_two_le hf), hw.card_eq]

end Assembly
end CFSG.SeitzReduction.F4Pilot
end
