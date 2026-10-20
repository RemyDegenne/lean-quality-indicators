@[expose] public section

namespace RellichKondrachov

namespace Analysis

namespace FunctionalSpaces

namespace Sobolev

namespace Euclidean

open scoped ENNReal MeasureTheory

open MeasureTheory

section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceH2 : MeasurableSpace E := borel E

local instance instBorelSpaceH2 : BorelSpace E := ⟨rfl⟩

local instance instOpensMeasurableSpaceH2 : OpensMeasurableSpace E := by infer_instance

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- The continuous gradient map `H² → L²(E)`. -/
noncomputable def h2ToL2Grad : (↥(h2 (μ := μ) (E := E))) →L[ℝ] L2E (μ := μ) :=
  (ContinuousLinearMap.fst ℝ (L2E (μ := μ)) (L2EE (μ := μ))).comp
    ((ContinuousLinearMap.snd ℝ (L2ℝ (μ := μ)) (L2E (μ := μ) × L2EE (μ := μ))).comp
      (Submodule.subtypeL (h2 (μ := μ) (E := E))))

end
end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
end
