noncomputable section

open Complex Real MeasureTheory LanglandsTunnell.TateLocal

namespace LanglandsTunnell.ArchPlace

def realGammaAt (μ : Measure ℝ) (ψ : AddChar ℝ ℂ) (f₀ : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  realZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / realZeta μ f₀ χ s

end LanglandsTunnell.ArchPlace
end
