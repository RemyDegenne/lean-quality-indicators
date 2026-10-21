namespace OAI

namespace SingleFold.Counter

open Packed

variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]

variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}

namespace System

section

variable (h : System M d v)

include h

lemma width : 0 < v.w := by
  by_contra hh
  have hw : v.w=0 := by omega
  have := h.power
  rw [hw,pow_zero] at this
  have := h.Bfour
  omega

end
end System
end SingleFold.Counter
end OAI
