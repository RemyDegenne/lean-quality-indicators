set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open ModularCurve WeierstrassCurve Polynomial

open scoped Classical

namespace ModularCurve.TatePoint

theorem charZero_H : CharZero H :=
  (RingHom.charZero_iff (HahnSeries.C (R := Qbar) (Γ := ℚ)).injective).mp inferInstance

end ModularCurve.TatePoint
end
