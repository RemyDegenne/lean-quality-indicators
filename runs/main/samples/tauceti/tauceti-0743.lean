public section

namespace TauCeti.Toric

open Topology

variable {N N' ι : Type*} [AddCommGroup N] [AddCommGroup N']

variable (e : IntegralCharacter N ≃+ (ι →₀ ℤ))

@[simp]
theorem coe_complexTorusCoordinatesContinuousMulEquiv :
    ⇑(complexTorusCoordinatesContinuousMulEquiv e) = complexTorusCoordinates e :=
  (rfl)

end TauCeti.Toric
end
