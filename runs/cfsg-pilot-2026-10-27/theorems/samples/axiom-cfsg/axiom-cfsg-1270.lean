public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

open scoped commutatorElement

variable {F : Type} [Field F] [Finite F]

section Overgroup

variable {K : Subgroup (PGammaL2 F)}

theorem orderOf_eq_two_pow_of_mem_galTwo {σ : F ≃+* F} (hσ : σ ∈ galTwo F) :
    ∃ i : ℕ, orderOf σ = 2 ^ i := by
  obtain ⟨k, hk⟩ := hσ
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact ⟨i, hi⟩

end Overgroup
end CFSG.ComponentClassification.AutL2Facts
end
