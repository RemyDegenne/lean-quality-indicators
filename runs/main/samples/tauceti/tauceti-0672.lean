public section

namespace TauCeti

universe u v

namespace IsProP

section Group

variable {p : ℕ} [hp : Fact p.Prime] {A : Type u} [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A]

variable [TotallyDisconnectedSpace A]

theorem eq_zero_of_padicPow_mem (hA : IsProP p A) {H : Subgroup A} (hH : IsClosed (H : Set A))
    {a : A} (ha : ∀ k : ℕ, a ^ p ^ k ∉ H) {l : ℤ_[p]} (hl : hA.padicPow a l ∈ H) : l = 0 := by
  by_contra hne
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[p]ˣ, l = u * (p : ℤ_[p]) ^ l.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hne⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ, l.valuation = v := ⟨_, rfl⟩
  rw [hv] at hu
  refine ha v ?_
  -- `pᵛ = l · u⁻¹`, so `a ^ (pᵛ)` is a `p`-adic power of `a ^ l ∈ H`.
  have hpv : (p : ℤ_[p]) ^ v = l * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [hu, mul_comm (u : ℤ_[p]), mul_assoc, Units.mul_inv, mul_one]
  rw [← hA.padicPow_natCast, Nat.cast_pow, hpv, hA.padicPow_mul]
  exact hA.padicPow_mem hH hl _

end Group
end IsProP
end TauCeti
end
