public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits CFSG.Fischer
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary.SUExtras

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

attribute [local instance high] f4DecEq

theorem range_thetaK :
    thetaK.range = G0c := by
  refine Subgroup.eq_of_le_of_card_ge (range_le_of_roots thetaK fun γ hγ x hx => ?_) ?_
  · obtain ⟨r, rfl⟩ := (mem_su6D_roots_iff' γ).1 hγ
    rw [thetaK_root r hx]
    exact xRootK_mem_G0c_lt r.isLt (su6Entry r x).code.isLt
  · rw [card_G0c, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange thetaK).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq ker_thetaK).toEquiv,
      natCard_SU6_quot_center]

end CFSG.Sporadic.Co2Smith
end
