set_option maxHeartbeats 200000

set_option synthInstance.maxHeartbeats 20000

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve.MultCovering

section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

def zeroChart :
    ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  (infChart Γ).comap (frickeInvolutionBar (1 * p))

end PerA
end ModularCurve.MultCovering
end
