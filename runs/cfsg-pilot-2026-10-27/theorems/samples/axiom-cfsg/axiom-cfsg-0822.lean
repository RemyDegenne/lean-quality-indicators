public noncomputable section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LieType.CurtisTits

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TrialityClosed

attribute [local instance] TorusLift.centerCommGroup

theorem rep_r11 : rep r11 = d11 := by rw [rep, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

end CFSG.LieType.Steinberg.CentralExt.TrialityClosed
end
