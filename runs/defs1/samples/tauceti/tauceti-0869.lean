public section

noncomputable section

open MeasureTheory InformationTheory Set

open scoped ENNReal

namespace TauCeti

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {R P : Measure Ω} {e : Ω → X × Y} {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

/-- The value of the dynamic Schrödinger problem with reference measure `R` on `Ω` and endpoint map
`e : Ω → X × Y`: the infimum of the relative entropy `klDiv P R` over the measures `P` on `Ω` such
that the law `P.map e` of `e` couples `μ` and `ν`. It is `∞` when no such `P` has finite relative
entropy. -/
def dynamicSchroedingerValue (R : Measure Ω) (e : Ω → X × Y) (μ : Measure X) (ν : Measure Y) :
    ℝ≥0∞ :=
  ⨅ (P : Measure Ω) (_ : IsCoupling (P.map e) μ ν), klDiv P R

end TauCeti
end
end
