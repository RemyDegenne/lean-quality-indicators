public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

theorem isIntegral_ratCast_iff_den_eq_one {α : Type*} [DivisionRing α] [CharZero α] (q : ℚ) :
    IsIntegral ℤ (q : α) ↔ q.den = 1 := by
  rw [isIntegral_ratCast_iff_exists_int, Rat.den_eq_one_iff]
  exact ⟨fun ⟨n, hn⟩ => by rw [hn]; simp, fun h => ⟨q.num, h.symm⟩⟩

end CFSG.FeitThompson
end
