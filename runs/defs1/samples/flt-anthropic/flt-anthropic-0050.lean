set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]

def ofMv (t : MvPowerSeries (Fin 1) R) : PowerSeries R := killCompl e1 t

end MvFormalGroup
end
