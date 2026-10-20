@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

namespace HigherHarmonicYoung

section

open scoped BigOperators

/-- The inner product core on row-multihomogeneous polynomials induced by their coefficient
embedding. -/
@[implicit_reducible] def youngMultihomogeneousFischerCore
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    InnerProductSpace.Core ℝ (youngMultihomogeneousSubmodule n lam) :=
  SpherePacking.Fischer.embeddingInnerCore
    (youngMultihomogeneousCoefficientEmbedding n lam)
    (youngMultihomogeneousCoefficientEmbedding_injective n lam)

end
end HigherHarmonicYoung
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
