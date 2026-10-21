namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set

open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem totalVolume_le_actualJacobiIntegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    totalVolume g ≤ (2 * Real.pi ^ 2) *
      ∫ r in (0 : ℝ)..Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o := by
  have h := volumeMeasure_le_canonicalRadialMass g o hRic
  rw [canonical_actualRadialMass_eq, ← ENNReal.ofReal_mul (by positivity)] at h
  have hn : 0 ≤ (2 * Real.pi ^ 2) *
      ∫ r in Icc (0 : ℝ) Real.pi, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  have hreal := ENNReal.toReal_le_of_le_ofReal hn h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    at hreal
  exact hreal

end
end PositiveEinsteinFour.Geometry
end
end OAI
