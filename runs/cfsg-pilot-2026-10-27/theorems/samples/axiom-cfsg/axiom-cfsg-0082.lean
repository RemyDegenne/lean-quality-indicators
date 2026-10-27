public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

theorem heBridge_parts :
    isInvA 8330 heBridgeArr (invCand 8330 heBridgeArr) = true ∧
    (∀ i < 8330, ap CFSG.Sporadic.He.orb.alpha heBridgeArr[i]! =
      heBridgeArr[(heGen 0)[i]!]!) ∧
    (∀ i < 8330, ap CFSG.Sporadic.He.orb.beta heBridgeArr[i]! =
      heBridgeArr[(heGen 1)[i]!]!) := by
  rw [orb_eq]
  exact heBridge_parts'

end CFSG.Sporadic.HeldB
end
