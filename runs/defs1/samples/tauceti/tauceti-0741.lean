public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

universe u v

/-- A finite-`p` measured-kernel presentation on a standard Borel probability carrier.
The target needs no separability or completeness. Presentations themselves are not identified
under null changes or measure-preserving parametrizations; `GromovWassersteinSpace` makes
exactly those identifications. -/
structure GromovWassersteinPresentation (p : ℝ≥0∞) (Z : Type v) [MetricSpace Z] where
  /-- The measurable carrier of the kernel. -/
  Carrier : Type u
  /-- The sigma-algebra on the carrier. -/
  [measurableSpace : MeasurableSpace Carrier]
  /-- Standard Borel structure supplies coupling gluing and attainment. -/
  [standardBorelSpace : StandardBorelSpace Carrier]
  /-- The probability law on the carrier. -/
  measure : Measure Carrier
  /-- The carrier law has total mass one. -/
  [isProbabilityMeasure : IsProbabilityMeasure measure]
  /-- The target-valued kernel, with no symmetry assumption. -/
  kernel : Carrier × Carrier → Z
  /-- Strong measurability is needed only almost everywhere on the square. -/
  aestronglyMeasurable_kernel : AEStronglyMeasurable kernel (measure.prod measure)
  /-- Finite size about some target point, including essential boundedness at infinity. -/
  finite_moment : ∃ z : Z, MemLp (fun q ↦ edist (kernel q) z) p (measure.prod measure)

end TauCeti
end
end
