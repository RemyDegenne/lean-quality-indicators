set_option warningAsError true

namespace PowerSeries

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Native unit with underlying series `1 - C a * X`, using the geometric-series unit. -/
public noncomputable def oneSubCXUnit (a : R) : (PowerSeries R)ˣ :=
  Units.map (rescale a).toMonoidHom (invOneSubPow R 1)⁻¹

end PowerSeries
