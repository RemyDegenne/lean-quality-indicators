@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

open MeasureTheory

open TauCeti.DavisKahan

open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace FreeBeam

namespace Model

section

/-- The unit-interval coordinate, clamped so that the symbol is globally bounded. -/
noncomputable def beamClamp (t : ℝ) : ℝ := max 0 (min t 1)

end
end Model
end FreeBeam
end DavisKahan
end TauCeti
end
