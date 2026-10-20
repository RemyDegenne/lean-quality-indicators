@[expose] public section

namespace Bananas

open Utilities

theorem sectionFive_inversion_lower_bound_of_involutive_transmission
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ} {k : ℕ}
    (hk : 0 < k) (hconn : _root_.graphConnected M.graph)
    (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau)
    (hInvolutive : ∀ a b : ℤ, tau b = a ↔ tau a = b) :
    sectionFiveRankDropSum M D k ≤ kInversionCount k tau := by
  exact sectionFive_inversion_lower_bound_of_involutive_transmission_connected
    hk hconn hTau hAffine hInvolutive

end Bananas
end
