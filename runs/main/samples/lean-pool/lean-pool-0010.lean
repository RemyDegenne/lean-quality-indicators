@[expose] public section

noncomputable section

open MeasureTheory

attribute [local instance] realModesMeasureSpace realModesMeasureIsAddHaar realModesProbability

namespace AVenhance.Infra.Parabolic.FourierGalerkin

theorem Modes.mFourier_star_at (k : Fin 2 → ℤ) (x : Torus) :
    star (UnitAddTorus.mFourier k x) = UnitAddTorus.mFourier (-k) x := by
  rw [Complex.star_def]
  exact (UnitAddTorus.mFourier_neg (n := k) (x := x)).symm

end AVenhance.Infra.Parabolic.FourierGalerkin
end
end
