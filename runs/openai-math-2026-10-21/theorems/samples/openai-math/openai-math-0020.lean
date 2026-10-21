namespace OAI

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular

open scoped Manifold ContDiff

noncomputable section

local instance : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalCurvatureDerivative_mean_square
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hTs : ∀ a, (plusWeylGradient g c e a)ᵀ = plusWeylGradient g c e a)
    (hTt : ∀ a, (plusWeylGradient g c e a).trace = 0) :
    (∫ q, squareNorm (normalCurvatureDerivative g c e q) ∂sphereMeasure) =
      (gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e)) / 16 := by
  exact integral_normalDerivative_squareNorm_exact h _ _ hTs hTt

end
end PositiveEinsteinFour.Geometry
end OAI
