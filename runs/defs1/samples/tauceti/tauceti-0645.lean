public section

noncomputable section

open MeasureTheory InformationTheory Filter Topology

open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c c' : X × Y → ℝ≥0∞} {ε ε' : ℝ≥0} {π R : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

/-- The value of the static Schrödinger problem with reference measure `R`: the infimum of the
relative entropy `klDiv π R` over the couplings `π` of `μ` and `ν`. It is `∞` when `μ` and `ν`
have no coupling, or no coupling of finite relative entropy. -/
def schroedingerValue (R : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), klDiv π R

end TauCeti
end
end
