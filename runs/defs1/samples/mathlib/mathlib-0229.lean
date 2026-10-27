@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Square

variable {C : Type*} [Category* C] [Preadditive C]
  (sq : Square C) [HasBinaryBiproduct sq.X₂ sq.X₃]

variable {sq} in
/-- The colimit cokernel cofork attached to a pushout square. -/
noncomputable def IsPushout.isColimitCokernelCofork (h : sq.IsPushout) :
    IsColimit sq.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

end Square
end CategoryTheory
end
