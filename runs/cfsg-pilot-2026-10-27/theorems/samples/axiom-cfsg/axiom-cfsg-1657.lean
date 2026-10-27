public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

lemma one_add_pow_two_pow_eq_two_mul_odd {u : ℕ} (hu : Odd u) (e : ℕ) :
    ∃ b, Odd b ∧ 1 + u ^ 2 ^ (e + 1) = 2 * b := by
  have h : (u ^ 2 ^ e) ^ 2 % 8 = 1 := odd_sq_mod_eight (hu.pow)
  have hv : u ^ 2 ^ (e + 1) % 8 = 1 := by
    rw [← pow_mul, show 2 ^ e * 2 = 2 ^ (e + 1) by rfl] at h
    exact h
  have hv' : u ^ 2 ^ (e + 1) = 8 * (u ^ 2 ^ (e + 1) / 8) + 1 := by
    have := Nat.div_add_mod (u ^ 2 ^ (e + 1)) 8
    omega
  refine ⟨4 * (u ^ 2 ^ (e + 1) / 8) + 1, ⟨2 * (u ^ 2 ^ (e + 1) / 8), by ring⟩, ?_⟩
  omega

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
end
