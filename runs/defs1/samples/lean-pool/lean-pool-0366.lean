@[expose] public section

universe u

open MeasureTheory

/-- Product measure on a pair of independent ghost samples. -/
noncomputable abbrev GhostPairMeasure
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (m : ℕ) :
    MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))

end
