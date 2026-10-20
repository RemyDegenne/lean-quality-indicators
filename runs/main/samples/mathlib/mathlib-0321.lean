@[expose] public section

namespace OrdinalApprox

universe u

variable {α : Type u}

variable [CompleteLattice α] (f : α →o α) {x : α} {a b c : Ordinal.{u}}

open Function fixedPoints Cardinal Order OrderHom

theorem apply_lfpApprox_le_lfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    f (lfpApprox f x a) ≤ lfpApprox f x b := by
  nth_rw 2 [lfpApprox]
  exact le_sup_of_le_right <| le_iSup₂_of_le a h le_rfl

end OrdinalApprox
end
