public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  (H : HeegaardRegionSystem n Point Region Basepoint)

section CurveHomology

/-- The class of a `1`-cycle of `α ∪ β` in `CurveHomology`. -/
def CurveHomology.mk : H.arcCycles →+ H.CurveHomology :=
  QuotientAddGroup.mk' _

end CurveHomology
end HeegaardRegionSystem
end TauCeti
end
