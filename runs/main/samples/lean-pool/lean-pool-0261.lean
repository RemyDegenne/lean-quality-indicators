@[expose] public section

namespace TMB

theorem _root_.Bananas.TwiceMarkedBananas.s5_lem5_3_1
    {M : TwiceMarked} (hconn : graphConnected M.graph)
    (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau)
    (hDual : linearEquiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D)
      (transmissionDualDivisor M.u M.v D)) :
    ∀ a b : ℤ, tau b = a ↔ tau a = b := by
  exact Bananas.sectionFive_tau_involutive_of_dual_automorphism (M := toLibTM M) hconn
    (toLibSwap phi) ((isTransmissionPermutation_toLib _ _ _).mp hTau) hDual

end TMB
end
