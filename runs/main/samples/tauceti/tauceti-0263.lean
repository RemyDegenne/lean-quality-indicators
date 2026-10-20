public section

namespace MultilinearMap

section SignedSuspension

variable {R : Type uR} [CommRing R]

@[simp]
theorem suspend_suspend {k : ℕ} {M : Fin k → Type uM} {N : Type uN}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [AddCommMonoid N] [Module R N]
    (d : ℕ → ℤ) (f : MultilinearMap R M N) : suspend d (suspend d f) = f := by
  rw [suspend_eq_smul, suspend_eq_smul, smul_smul, ← TauCeti.negOnePowCast_add, ← two_mul,
    TauCeti.negOnePowCast_two_mul, one_smul]

end SignedSuspension
end MultilinearMap
end
