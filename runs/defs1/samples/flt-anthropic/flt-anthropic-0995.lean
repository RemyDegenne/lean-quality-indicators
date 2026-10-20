set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

variable {W : Type u} [CommRing W]

def nfCoeff (ab : PowerSeries W × PowerSeries W) : ℤ → W
  | Int.ofNat i => PowerSeries.coeff i ab.1
  | Int.negSucc j => PowerSeries.coeff (j + 1) ab.2

end
end ModularCurve.UVCrossingModel
