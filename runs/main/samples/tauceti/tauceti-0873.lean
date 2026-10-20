public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal

namespace TauCeti

theorem isCompleteBernsteinFunction_stieltjesBernsteinTransform
    {μ : Measure ℝ≥0} {a b : ℝ≥0} (hzero : μ {0} = 0)
    (hμ : Integrable stieltjesWeight μ) :
    IsCompleteBernsteinFunction (stieltjesBernsteinTransform μ a b) :=
  ⟨a, b, μ, representsCompleteBernstein_stieltjesBernsteinTransform hzero hμ⟩

end TauCeti
end
end
