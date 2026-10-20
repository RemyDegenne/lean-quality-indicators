@[expose] public section

open Set hiding restrict restrict_apply

open Filter ENNReal Topology NNReal

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α β γ : Type*}

open SimpleFunc

variable {m : MeasurableSpace α} {μ ν : Measure α} {s : Set α}

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => lintegral μ r

@[inherit_doc MeasureTheory.lintegral]
notation3 "∫⁻ "(...)", "r:60:(scoped f => lintegral volume f) => r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => lintegral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.lintegral]
notation3"∫⁻ "(...)" in "s", "r:60:(scoped f => lintegral (Measure.restrict volume s) f) => r

theorem lintegral_zero_fun : lintegral μ (0 : α → ℝ≥0∞) = 0 :=
  lintegral_zero

end MeasureTheory
end
