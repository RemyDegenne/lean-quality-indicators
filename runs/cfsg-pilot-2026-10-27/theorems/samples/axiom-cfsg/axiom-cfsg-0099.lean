public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic

section Swaps

variable {n : ℕ}

theorem isSwap_iff_exists {t : Equiv.Perm (Fin n)} :
    t.IsSwap ↔ ∃ x y, x ≠ y ∧ t = Equiv.swap x y :=
  Iff.rfl

end Swaps
end CFSG.ClassicalInvolution.Models
end
