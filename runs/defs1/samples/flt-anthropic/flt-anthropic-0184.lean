set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open HahnSeries IntermediateField

open scoped Matrix

namespace ModularCurve

variable (q : ℕ) [Fact q.Prime]

variable (M' : ℕ)

def levelComponentField (L : Type) [Field L] [Algebra ℚ L] (ι : CyclotomicField q ℚ →ₐ[ℚ] L) :
    IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffMap (ι : CyclotomicField q ℚ →+* L)) ''
    (levelFunctionField q M' : Set (LaurentSeries (CyclotomicField q ℚ))))

end ModularCurve
end
