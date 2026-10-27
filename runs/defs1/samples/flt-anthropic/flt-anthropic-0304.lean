set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve

namespace PhiGen

section CosetIndex

variable (ℓ : ℕ)

def cosetB (i : Fin (ℓ + 1)) : ℕ := if i = 0 then 0 else (i : ℕ) - 1

end CosetIndex
end PhiGen
end ModularCurve
end
