namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory

open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem actual_scalar_divergence_distribution [T3Space M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
    [PreconnectedSpace M] (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ b : Lp ℝ 2 (normalizedVolume g), ∀ (c : M) (ψ : FourSpace → ℝ)
      (_hψ : ContDiff ℝ ∞ ψ) (_hc : HasCompactSupport ψ)
      (_hs : tsupport ψ ⊆ (chartAt FourSpace c).target),
      (∫ z in (chartAt FourSpace c).target, b ((chartAt FourSpace c).symm z) *
        ∑ i, partialDeriv (fun w => ∑ j,
          chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        ((smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a).val
          ((chartAt FourSpace c).symm z) * ψ z) := by
  obtain ⟨b, hb⟩ := actual_scalar_coordinate_distribution g o hRic a
  refine ⟨b, ?_⟩
  intro c ψ hψ hc hs
  rw [← hb c ψ hψ hc hs]
  apply MeasureTheory.setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  dsimp only
  rw [scalarChartOperator_divergence g c ψ z hz hψ.contDiffAt]
  ring

end
end PositiveEinsteinFour.Geometry
end
end OAI
