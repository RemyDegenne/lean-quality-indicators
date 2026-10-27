@[expose] public section

namespace Connes

namespace PaperChartMeasure

open MeasureTheory

open Construction

open Construction.PaperKernel

open BinaryPontryaginDual

open PaperDualHaar

open PaperDualTopology

noncomputable section

/-- Invariant probability measure for the additive character action, whose
measurability is recorded above. Paper: §4.
-/
def IsInvariantPaperSpectralMeasure {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D))
    (μ : ProbabilityMeasure CharacterSpace) : Prop :=
  ∀ h : H,
    (μ : Measure CharacterSpace).map (paperDualCharacterAction action h) = μ

end
end PaperChartMeasure
end Connes
end
