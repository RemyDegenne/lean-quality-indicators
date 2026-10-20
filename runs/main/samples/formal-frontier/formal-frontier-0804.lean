set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

@[simp]
theorem x₁_apply_even (v : ℕ →₀ M) (n : ℕ) : x₁ S M v (2 * n) = 0 := by
  have coordinate := congrArg (fun pair : (ℕ →₀ M) × (ℕ →₀ M) => pair.1 n)
    (parityEquiv_x₁ S M v)
  simpa only [parityEquiv_fst_apply, Prod.fst, Finsupp.zero_apply] using coordinate

end CountableEndomorphism
end
