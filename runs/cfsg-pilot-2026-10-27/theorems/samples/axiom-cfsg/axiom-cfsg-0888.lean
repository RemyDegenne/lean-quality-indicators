public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem le_of_pow_dvd_ree_shape {p a j : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (h : p ^ j ∣ (p ^ a) ^ 3 * ((p ^ a) ^ 3 + 1) * (p ^ a - 1)) : j ≤ 3 * a := by
  have e0 : (p ^ a) ^ 3 = p ^ (3 * a) := by rw [← pow_mul, mul_comm]
  have e : (p ^ a) ^ 3 * ((p ^ a) ^ 3 + 1) * (p ^ a - 1) =
      p ^ (3 * a) * (((p ^ a) ^ 3 + 1) * (p ^ a - 1)) := by
    rw [mul_assoc]; exact congrArg (· * _) e0
  rw [e] at h
  refine pow_dvd_of_pow_dvd_pow_mul_coprime hp ?_ h
  intro hdvd
  have hpa : p ∣ p ^ a := dvd_pow_self p (by omega)
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · have h2 : p ∣ (p ^ a) ^ 3 := hpa.pow (by norm_num)
    have := (Nat.dvd_add_right h2).mp h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · have h5 := Nat.dvd_sub hpa h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

end CFSG.AGLEmbedding
end
