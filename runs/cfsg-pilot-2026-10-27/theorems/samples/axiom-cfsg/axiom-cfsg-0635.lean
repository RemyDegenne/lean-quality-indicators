public section

namespace CFSG.LieType.Universal.Unitary.SUExtras

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

variable (hσ : ∀ c, σ (σ c) = c)

theorem mat_apply_self_of_mem_rootGroup {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0)
    {x : SU σ n} (hx : x ∈ rootGroup σ hσ n γ) (a : Fin n) : mat σ n x a a = 1 := by
  rw [mat_apply_of_mem_rootGroup hσ hx, one_apply_eq]
  · rw [sub_self]
    exact fun h => hγ h.symm
  · rw [sub_self]
    exact fun h => hγ (eq_zero_of_two_nsmul_eq_zero h)

end CFSG.LieType.Universal.Unitary.SUExtras
end
