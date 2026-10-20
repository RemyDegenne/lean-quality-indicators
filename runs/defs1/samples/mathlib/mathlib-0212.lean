@[expose] public section

namespace ComplexShape

/-- For `l : ℕ` and `u : ℤ × ℤ`, this is the complex shape on `ℤ × Fin l`, which
connects `a` to `b` when the equality `a + u = b` holds in `ℤ × ℤ`. -/
def spectralSequenceFin (l : ℕ) (u : ℤ × ℤ) : ComplexShape (ℤ × Fin l) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2.1 + u.2 = b.2.1
  next_eq _ _ := by ext <;> lia
  prev_eq _ _ := by ext <;> lia

end ComplexShape
end
