universe u

public noncomputable section

namespace Surreal

open OmnificInteger

theorem isOmnificInteger_mk_iff (x : IGame.{u}) [IGame.Numeric x] :
    IsOmnificInteger (Surreal.mk x) ↔
      x ≈ !{{x - 1} | {x + 1}} := by
  rw [IsOmnificInteger, omnificIntegerCut_mk, Surreal.mk_eq_mk]
  rfl

end Surreal
end
