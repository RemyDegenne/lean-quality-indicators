@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

namespace FanDominanceExploration

open scoped ENNReal InnerProductSpace

noncomputable section

universe v

local instance instCompleteSpaceFiniteFanDominance
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] : CompleteSpace E :=
  FiniteDimensional.complete ℂ E

/-- Total-gauge form of: if one of the displayed source norms does not exist,
the comparison is treated as vacuous; otherwise the Fan inequality must hold.
This proposition records the partial-norm convention explicitly. -/
def HasFanDominanceWithVacuity
    (N : NormalizedSymmetricOperatorIdealFamily.{0, v} ℂ) : Prop :=
  ∀ {E F E' F' : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
    {A : E →L[ℂ] F} {B : E' →L[ℂ] F'},
    (∀ k, kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B) →
      (N.toSymmetricOperatorIdealFamily.gauge A = ⊤ ∨
        N.toSymmetricOperatorIdealFamily.gauge B = ⊤) ∨
      N.toSymmetricOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.gauge B

end
end FanDominanceExploration
end ExactSinTheta
end DavisKahan
end TauCeti
end
