namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormKernelAction_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem twoFormHeatKernel_pairing_integral (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (u v : smoothTwoForms o) :
    (∫ z : M × M, inner ℝ (v.val z.1)
      (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2))
      ∂(normalizedVolume g).prod (normalizedVolume g)) =
      inner ℝ (twoFormHeat hRic t (smoothTwoFormToL2 (u : SmoothL2TwoForm o)))
        (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) := by
  have he : (fun z : M × M => inner ℝ (v.val z.1)
      (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2))) =
      (fun z => ∑' i, twoFormHeatKernelPairingTerm hRic t u v i z) :=
    funext fun z => (twoFormHeatKernel_pairing_hasSum hRic t ht u v z).tsum_eq.symm
  rw [he, ← integral_tsum_of_summable_integral_norm
    (fun i => twoFormHeatKernelPairingTerm_integrable hRic t u v i)
    (twoFormHeatKernelPairingTerm_integral_norm_summable hRic t ht u v)]
  simp_rw [twoFormHeatKernelPairingTerm_integral]
  exact (twoFormHeat_pairing_tsum hRic t _ _).symm

end
end PositiveEinsteinFour.Geometry
end
end OAI
