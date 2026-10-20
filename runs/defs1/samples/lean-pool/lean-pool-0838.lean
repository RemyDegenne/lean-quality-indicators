@[expose] public section

namespace HsVirial

open Set

open Metric

open MeasureTheory

open scoped BigOperators ENNReal

noncomputable section

/-- Reindex a position array before separating paired and single blocks. -/
def hardSphereReindexedBlockCoordinateEquiv
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n) :
    (Fin n → HSPosition 3) ≃ᵐ
      ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3)) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin n => HSPosition 3) e).symm.trans
    (hardSphereBlockCoordinateEquiv m q)

end
end HsVirial
end
