namespace OAI

open Set MeasureTheory

open scoped InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (M : PositiveBilinearMeasure X E)

theorem cutoffHeatMass_energy {t : ℝ} (ht : 0 < t) (x : X) (v : E) :
    ⟪v, cutoffHeatMass μ hQ hp hχ hsχ M ht x v⟫_ℝ =
      ∫ y, (χ y * p t x y) ∂(M.measure v) :=
  M.weightedOperator_energy _ v

end RegularPointCoordinates
end
end OAI
