public section

namespace TauCeti

variable {k : ℕ} {a b c d i j : Fin k}

@[simp]
theorem capCup_val_inl_of_ne (hia : i ≠ a) (hib : i ≠ b) :
    (capCup a b).val (Sum.inl i) = Sum.inr i := by
  simp [capCup_val_apply, Equiv.swap_apply_of_ne_of_ne, hia, hib]

end TauCeti
end
