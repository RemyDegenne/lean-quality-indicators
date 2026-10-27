set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

/-- Embed a finitely supported sequence into the even coordinates. -/
noncomputable def x₀ : Module.End S (ℕ →₀ M) :=
  (parityEquiv S M).symm.toLinearMap.comp (LinearMap.inl S (ℕ →₀ M) (ℕ →₀ M))

end CountableEndomorphism
end
