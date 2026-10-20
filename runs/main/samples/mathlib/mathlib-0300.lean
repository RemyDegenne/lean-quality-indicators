public section

open Ideal

variable {R : Type*}

namespace Int

section Ring

variable [Ring R] {I : Ideal R}

variable (I)

theorem _root_.Ideal.ringChar_quot {S : Type*} [CommRing S] (I : Ideal S) :
    ringChar (S ⧸ I) = absNorm (under ℤ I) := by
  refine ringChar.eq_iff.mpr <| (charP_iff _ _).mpr fun x ↦ ?_
  change Ideal.Quotient.mk I x = 0 ↔ _
  rw [Quotient.eq_zero_iff_mem, ← Int.cast_natCast, cast_mem_ideal_iff, natCast_dvd_natCast]

end Ring
end Int
end
