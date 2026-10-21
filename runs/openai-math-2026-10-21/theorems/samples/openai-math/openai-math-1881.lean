namespace OAI

section

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory

open scoped Topology NNReal ENNReal unitInterval

namespace SLEExactGauge.MeshSlab

open FiniteTilt

local instance meshExponentsDensityRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _

local instance meshExponentsDensityRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩

local instance meshExponentsDensityComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _

local instance meshExponentsDensityComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

lemma physicalValue_real_tendsto {Ω : Type*}
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ)
    (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    {e : ℝ} (he : 0 < e) (hes : e < z.im)
    (hr : (2*z.im)*Real.exp (-u) < e/4)
    (Cs : ℕ → Cutoff z u) (hCs : Tendsto (fun n => (Cs n).angle) atTop (𝓝 0)) :
    Tendsto (fun n => (Cs n).physicalValue κ B γ e ω) atTop
      (𝓝 (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal) := by
  have hh := tendsto_physicalValue_killed_general κ B γ g f ω hm hz hu hc hb0 he hes hr Cs hCs hκ
  have ht := (ENNReal.continuousAt_toReal (physicalStoppedDensity_ne_top κ (fun t => B t ω)
    (γ ω) (g ω) z e)).tendsto.comp hh
  simpa only [Function.comp_def,ENNReal.toReal_ofReal ((Cs _).physicalValue_nonneg κ B γ e ω)] using ht

end SLEExactGauge.MeshSlab
end
end
end OAI
