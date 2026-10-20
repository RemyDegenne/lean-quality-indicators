@[expose] public section

universe u v w

open Module Polynomial

variable (k : Type u) [Field k]

namespace IsAlgClosed

variable {k}

theorem roots_eq_zero_iff_natDegree_eq_zero [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p.natDegree = 0 :=
  roots_eq_zero_iff.trans eq_C_coeff_zero_iff_natDegree_eq_zero

end IsAlgClosed
end
