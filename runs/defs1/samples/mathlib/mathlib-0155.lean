@[expose] public section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The length of a module, defined as the krull dimension of its submodule lattice. -/
noncomputable
def Module.length : ℕ∞ :=
  (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])

end
