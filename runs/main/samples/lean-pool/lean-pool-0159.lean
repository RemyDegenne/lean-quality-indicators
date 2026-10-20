@[expose] public section

noncomputable section

namespace NavierStokes.TemporalMeanUpdate

open Set Filter MeasureTheory Function

open TorusInverse

open scoped Topology ContDiff BigOperators Interval

section CompleteWeightedUpdate

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

theorem meanClass_axialAlias {a b d cL cR h α : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε R : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hR : ∀ n, 1 ≤ R n)
    (hscale : ∀ n, ChartScales.S n ≤ R n) (M : ℕ → ℝ) (hM : ∀ n, M n ≠ 0)
    {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α f)
    (hfc : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hs : ∀ n, RadialAlias.RadiallySupported a b (f n)) :
    WeightedClasses.MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε R hε hεone hR) α
      (fun n => axialAlias d a b (M n) (vector .radial) h n (f n)) := by
  let st := WeightedRadialPrimitive.logStripData (E := S × Plane) a b cL cR ha hcL hcR ε R hε hεone
      hR
  let g := fun n => desiredIncrement h n (f n)
  have hg : WeightedClasses.MeanClass st α g :=
    meanClass_desiredIncrement ha hcL hcR hh ε R hε hεone hR hscale hf hfc hp
  have hgc := fun n => desiredIncrement_smooth h n (hfc n) (hp n)
  have hgp := fun n => desiredIncrement_periodic h n (f n)
  have hgs := fun n => desiredIncrement_supported h n (hs n)
  have hw : WeightedClasses.MeanClass st α (fun n => PressureStream.weightedSource (g n)) := by
    unfold PressureStream.weightedSource
    simpa only [smul_eq_mul, id_eq] using
      meanClass_radialMultiply a b (φ := id) contDiff_id
        (s := st) (fun z hz => ⟨hz.1.le, hz.2.le⟩) hgc hg
  have hwm : ∀ n p, PressureStream.torusAverage (PressureStream.weightedSource (g n)) p = 0 := by
    intro n p
    rw [PressureStream.torusAverage_weightedSource, desiredIncrement_zeroMean h n (hfc n) (hp n),
        mul_zero]
  exact meanClass_dividedAlias ha hab hd hcL hcR ε R hε hεone hR M hM hw
    (fun n => PressureStream.weightedSource_contDiff (hgc n))
    (fun n => PressureStream.weightedSource_periodic (hgp n)) hwm
    (fun n => PressureStream.weightedSource_supported (hgs n))

end CompleteWeightedUpdate
end NavierStokes.TemporalMeanUpdate
end
end
