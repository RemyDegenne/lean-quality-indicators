@[expose] public section

variable {M : Type*} {N : Type*} {P : Type*}

open Function Setoid

namespace RingCon

section

variable [NonAssocSemiring M] [NonAssocSemiring N] [NonAssocSemiring P]

variable {c : RingCon M}

variable {f : M →+* P}

variable (c)

@[simp] theorem quotientQuotientEquivQuotient_coe_coe (c d : RingCon M) (h : c ≤ d) (x : M) :
    c.quotientQuotientEquivQuotient d h ↑(x : c.Quotient) = x :=
  rfl

end
end RingCon
end
