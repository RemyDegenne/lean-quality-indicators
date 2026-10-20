set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

section VariableSwap

variable {W : Type u} [CommRing W]

theorem uvSwapEquiv_C (w : W) :
    uvSwapEquiv (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = MvPowerSeries.C w := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_C]

end VariableSwap
end
end ModularCurve
