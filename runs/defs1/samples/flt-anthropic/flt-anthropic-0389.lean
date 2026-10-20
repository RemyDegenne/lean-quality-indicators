set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve

section AdjoinRing

abbrev adjoinJq : Subalgebra ℚ (LaurentSeries ℚ) := Algebra.adjoin ℚ {jq}

end AdjoinRing
end ModularCurve
end
