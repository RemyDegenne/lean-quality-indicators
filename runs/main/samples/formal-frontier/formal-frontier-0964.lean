set_option warningAsError true

@[expose] public section

namespace Module

universe u v

variable (R : Type u) [CommRing R] (P : Type v)
  [AddCommGroup P] [Module R P]

namespace Free

theorem of_finProdEquiv_of_stableRangeCondition
    {s n m : ℕ} (hs : Bass.StableRangeCondition R s) (hsn : s ≤ n)
    (e : (P × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R)) :
    Module.Free R P :=
  Module.Free.of_equiv
    (Module.finLinearEquivOfStableRangeCondition R P hs hsn e).symm

end Free
end Module
end
