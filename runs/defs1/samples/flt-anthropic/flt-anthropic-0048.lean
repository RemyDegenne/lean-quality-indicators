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

def nodeSrc (e : Fin (mAnnuli p)) : Place (IsLocalRing.ResidueField ↥A) (Fbar A (src p e)) :=
  charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p)

end PerA
end ModularCurve.MultCovering
end
