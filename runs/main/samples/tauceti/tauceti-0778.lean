public section

namespace TauCeti.Associative

section CentralCommutator

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z : A}

theorem isNilpotent_of_commutator_eq (hxy : x * y = y * x + z) (hxz : Commute x z)
    (hyz : Commute y z) (hx : IsNilpotent x) : IsNilpotent z := by
  obtain ⟨n, hn⟩ := hx
  -- Peel the powers of `x` off one at a time, trading each for a power of `z`.
  have hpeel : ∀ k ≤ n, x ^ (n - k) * z ^ k = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hn
    | succ k ih =>
      intro hk
      have heq : n - k = n - (k + 1) + 1 := by omega
      exact pow_mul_pow_succ_eq_zero_of_pow_succ_mul_pow_eq_zero hxy hxz hyz
        (by rw [← heq]; exact ih (by omega))
  exact ⟨n, by simpa using hpeel n le_rfl⟩

end CentralCommutator
end TauCeti.Associative
end
