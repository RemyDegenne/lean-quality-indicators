namespace P2MW.S_MvPowerSeries_isNoetherianRing_fin

set_option autoImplicit false

namespace W2MV

open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section Noetherian

theorem isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (isEmptyRingEquiv (Fin 0) R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccRingEquiv R n).symm

end Noetherian
end MvPowerSeries
end
end W2MV
end P2MW.S_MvPowerSeries_isNoetherianRing_fin
