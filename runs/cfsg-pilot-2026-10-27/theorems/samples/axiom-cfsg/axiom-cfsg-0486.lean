public noncomputable section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits MinData.Valid

open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField liftSL liftSL_injective map_liftSL)

open scoped MatrixGroups

variable {k : Type} [Field k] (θ : k →+* k)

theorem slRankOne_tv10 (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (tv 1 0 c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c := by
  rw [tv10_eq_sl2Lower]
  exact slRankOne_lower a c

end CFSG.ClassicalInvolution.WeakCT
end
