namespace P2MW.S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe

set_option autoImplicit false

universe u

namespace R4E1Ord

open Matrix

variable {p : ℕ} [hp : Fact p.Prime]

section Transport

variable {A : Type u} [Ring A] {n : Type} [Fintype n] [DecidableEq n]

variable (θ E : A →+* Matrix n n ℚ_[p]) (hθ : Function.Injective θ) (hE : Function.Injective E) (m : ℕ)
  (hθm : ∀ M : Matrix n n ℤ_[p], ∃ a : A, θ a = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p]))
  (hEint : ∀ a : A, ∃ M : Matrix n n ℤ_[p], E a = M.map ((↑) : ℤ_[p] → ℚ_[p]))

include hθ in
theorem DOf_natCast (k : ℕ) : DOf θ E m hθm hEint (k : ℤ_[p]) = 0 := by
  rw [DOf, Nat.cast_smul_eq_nsmul, FOf_nsmul θ E hθ, FOf_one θ E hθ, ← Nat.cast_smul_eq_nsmul ℤ_[p],
    smul_smul, mul_comm, sub_self]

end Transport
end R4E1Ord
end P2MW.S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
