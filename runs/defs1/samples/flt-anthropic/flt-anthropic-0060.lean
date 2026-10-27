set_option autoImplicit false

noncomputable section

open PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

def variableChangeDenom : R⟦X⟧ :=
  1 + PowerSeries.C C.s * (PowerSeries.X - PowerSeries.C C.r * W.formalW) + PowerSeries.C C.t * W.formalW

end WeierstrassCurve
end
