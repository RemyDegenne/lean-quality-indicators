@[expose] public section

open Function MeasureTheory Measure Real

open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR

namespace ProbabilityTheory

variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ

@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume

@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "; " μ "]" =>
  entropy X (μ[|Y ← y])

@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])

section condEntropy

variable [MeasurableSpace T]

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X`
conditioned on the
event `Y = y`. -/
noncomputable
def _root_.ProbabilityTheory.condEntropy
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y; μ]]

end condEntropy
end ProbabilityTheory
end
