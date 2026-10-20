@[expose] public section

noncomputable section

namespace BGS.FiniteField

open Polynomial

variable {F : Type*} [Field F]

local instance algebraicClosureDecidableEq :
    DecidableEq (AlgebraicClosure F) := Classical.decEq _

section FiniteBaseField

variable [Fintype F]

@[simp]
theorem legendrePointFrobenius_baseChange (u v : F)
    (P : (legendreWeierstrassCurve u v).toAffine.Point) :
    legendrePointFrobenius u v (legendrePointBaseChange u v P) =
      legendrePointBaseChange u v P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [legendrePointFrobenius, legendrePointBaseChange,
        mapLegendrePointCoordinates, AlgHom.commutes]

end FiniteBaseField
end BGS.FiniteField
end
end
