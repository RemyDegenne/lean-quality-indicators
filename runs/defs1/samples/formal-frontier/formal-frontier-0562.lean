set_option warningAsError true

namespace PowerSeries

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The negative logarithmic derivative weighted by `X`, on native units. -/
public noncomputable def negXLogDeriv (f : (PowerSeries R)ˣ) : PowerSeries R :=
  -X * derivative (f : PowerSeries R) * ((f⁻¹ : (PowerSeries R)ˣ) : PowerSeries R)

end PowerSeries
