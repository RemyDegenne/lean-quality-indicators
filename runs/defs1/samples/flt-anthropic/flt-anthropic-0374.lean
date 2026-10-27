set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

def const (π : W) (w : W) : UVCrossingModel W π := mk π (MvPowerSeries.C w)

end UVCrossingModel
end
end ModularCurve
