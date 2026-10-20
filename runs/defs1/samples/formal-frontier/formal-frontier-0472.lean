set_option warningAsError true

@[expose] public section

namespace Module

universe u v

variable (R : Type u) [CommRing R] (P : Type v)
  [AddCommGroup P] [Module R P]

/-- Cancel a finite free summand when a noetherian Krull-dimension upper bound
is strictly smaller than the number of remaining coordinates. -/
noncomputable def finLinearEquivOfKrullDimLE
    {d n m : ℕ} [IsNoetherianRing R] [Ring.KrullDimLE d R]
    (hdn : d + 1 ≤ n)
    (e : (P × (Fin m → R)) ≃ₗ[R] (Fin (n + m) → R)) :
    P ≃ₗ[R] (Fin n → R) :=
  finLinearEquivOfStableRangeCondition R P
    (Bass.stableRangeCondition_succ_of_krullDimLE (R := R) (d := d)) hdn e

end Module
end
