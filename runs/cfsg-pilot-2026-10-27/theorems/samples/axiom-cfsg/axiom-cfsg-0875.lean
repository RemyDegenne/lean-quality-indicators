public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16t3_pow_three_of_isPGroup_ker {P H : Type*} [Group P] [Group H] (β : P →* H)
    (hker : IsPGroup 2 β.ker) (hH : ∀ h : H, ∀ k : ℕ, h ^ 3 ^ k = 1 → h ^ 3 = 1) :
    ∀ p : P, ∀ k : ℕ, p ^ 3 ^ k = 1 → p ^ 3 = 1 := by
  intro p k hp
  have hβ : β (p ^ 3) = 1 := by
    rw [map_pow]
    exact hH (β p) k (by rw [← map_pow, hp, map_one])
  have hmem : p ^ 3 ∈ β.ker := MonoidHom.mem_ker.2 hβ
  obtain ⟨j, hj⟩ := hker ⟨p ^ 3, hmem⟩
  have h2 : orderOf (p ^ 3) ∣ 2 ^ j := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa using hj
  have h3 : orderOf (p ^ 3) ∣ 3 ^ k := by
    refine (orderOf_dvd_of_pow_eq_one ?_).trans (orderOf_dvd_of_pow_eq_one hp)
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ j) :=
    Nat.Coprime.pow k j ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))
  have hone : orderOf (p ^ 3) = 1 :=
    Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h2)
  exact orderOf_eq_one_iff.mp hone

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
