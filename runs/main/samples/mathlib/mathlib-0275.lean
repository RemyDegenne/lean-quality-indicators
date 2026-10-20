@[expose] public section

noncomputable section

open ENNReal MeasureTheory Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure

open TopologicalSpace hiding generateFrom

open Filter hiding prod_eq map

variable {α β γ : Type*}

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}

namespace MeasureTheory

namespace Measure

variable [hν : SFinite ν]

variable [SFinite μ]

lemma prod_smul_left {μ : Measure α} {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) : (c • μ).prod ν = c • (μ.prod ν) := by
  ext s hs
  rw [prod_apply hs, Measure.smul_apply, prod_apply hs]
  simp

end Measure
end MeasureTheory
end
end
