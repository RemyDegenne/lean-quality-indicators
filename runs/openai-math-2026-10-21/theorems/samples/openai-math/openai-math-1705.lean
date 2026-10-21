namespace OAI

section

noncomputable section

open scoped BigOperators Topology ENNReal

open MeasureTheory ProbabilityTheory Real Filter

namespace SKRatio.Gaussian

open Calculus

variable {n : ℕ}

lemma disorder_goe_hasLaw (β : ℝ) (n : ℕ) :
    HasLaw (SKRatioGaussian.goeDisorder (n := n) (β^2/(n:ℝ))) (disorderLaw β n)
      (SKRatioGaussian.gaussianCoordinates (SKRatioGaussian.MatrixCoordinates (Fin n))) :=
  SKRatioGaussian.goe_actual_disorder_hasLaw β n

end SKRatio.Gaussian
end
end
end OAI
