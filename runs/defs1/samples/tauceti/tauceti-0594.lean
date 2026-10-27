public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

section Definition

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {W W' : X × X → ℝ}
  {μ : Measure X}

/-- The *interaction energy* `(1 / 2) ∫∫ W(x, y) dμ(x) dμ(y)` of a measure `μ` in an interaction
kernel `W : X × X → ℝ`, as an extended real: the potential energy of `W / 2` against `μ ⊗ μ`. It is
`⊤` when the positive part of `W` has infinite integral against `μ ⊗ μ`. -/
def interactionEnergy (W : X × X → ℝ) (μ : Measure X) : EReal :=
  potentialEnergy (fun z ↦ W z / 2) (μ.prod μ)

end Definition
end TauCeti
end
end
