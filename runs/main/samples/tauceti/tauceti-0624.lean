public section

namespace TauCeti

namespace zHat

universe u

open Additive Multiplicative

section Components

variable (u : ∀ ℓ : Nat.Primes, ℤ_[ℓ])

theorem exists_forall_component_eq :
    ∃ a : Additive zHat.{u}, ∀ ℓ : Nat.Primes, component ℓ a = u ℓ := by
  -- The residues `residue u n` are compatible along divisibility, because both sides have the
  -- same reductions modulo the prime powers dividing the smaller level.
  obtain ⟨a, ha, -⟩ := existsUnique_forall_toZMod_eq (residue u) fun m n h ↦
    ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp hk hpk ↦ by
      have hcc := RingHom.congr_fun (ZMod.castHom_comp hpk h) (residue u n)
      simp only [RingHom.comp_apply, ZMod.castHom_apply] at hcc ⊢
      exact hcc.trans ((cast_residue u n ⟨p, hp⟩ hk (hpk.trans h)).trans
        (cast_residue u m ⟨p, hp⟩ hk hpk).symm)
  refine ⟨a, fun ℓ ↦ ?_⟩
  -- At the levels `ℓ ^ (k + 1)` the component of `a` reduces to the reduction of `u ℓ`; the
  -- level `ℓ ^ 0` follows by casting down.
  have hk (k : ℕ) :
      PadicInt.toZModPow (k + 1) (component ℓ a) = PadicInt.toZModPow (k + 1) (u ℓ) := by
    let n : ℕ+ := ⟨(ℓ : ℕ) ^ (k + 1), pow_pos ℓ.2.pos _⟩
    rw [← cast_toZMod_eq_toZModPow_component n dvd_rfl a, ha n,
      cast_residue u n ℓ k.succ_ne_zero dvd_rfl]
  refine PadicInt.ext_of_toZModPow.mp fun k ↦ ?_
  rw [← PadicInt.cast_toZModPow k (k + 1) k.le_succ, hk k]
  exact PadicInt.cast_toZModPow k (k + 1) k.le_succ (u ℓ)

end Components
end zHat
end TauCeti
end
