public section

section Tower

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Normal K L]
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

theorem AlgEquiv.restrictNormal_eq_one_iff_algebraMap (σ : M ≃ₐ[K] M) :
    σ.restrictNormal L = 1 ↔ ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
  constructor
  · intro h x
    rw [← AlgEquiv.restrictNormal_commutes σ L x, h, AlgEquiv.one_apply]
  · intro h
    ext x
    have hx := AlgEquiv.restrictNormal_commutes σ L x
    rw [h x] at hx
    exact (algebraMap L M).injective hx

end Tower
end
