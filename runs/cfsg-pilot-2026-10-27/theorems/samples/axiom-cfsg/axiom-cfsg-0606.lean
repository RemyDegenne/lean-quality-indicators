public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Subgroup

theorem commute_of_ker_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y G : Type*} [Group Y]
    [Group G] (θ : Y →* G) (hker : IsPGroup p θ.ker) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hTC : ∀ t ∈ T, ∀ c ∈ θ.ker, t * c = c * t) {Q : Subgroup Y}
    (hQ : ∀ t ∈ T, ∀ q ∈ Q, θ t * θ q = θ q * θ t) : ∀ t ∈ T, ∀ q ∈ Q, t * q = q * t := by
  intro t ht q hq
  set c : Y := t * q * t⁻¹ * q⁻¹ with hc
  have hcker : c ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hc]
    have h := hQ t ht q hq
    simp only [map_mul, map_inv]
    rw [h]
    group
  have htc : t * c = c * t := hTC t ht c hcker
  have h1 : t * q = c * q * t := by rw [hc]; group
  have hkey : ∀ k : ℕ, t ^ k * q = c ^ k * q * t ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc t ^ (k + 1) * q = t * (t ^ k * q) := by rw [pow_succ', mul_assoc]
        _ = t * (c ^ k * q * t ^ k) := by rw [ih]
        _ = (t * c ^ k) * q * t ^ k := by simp only [mul_assoc]
        _ = (c ^ k * t) * q * t ^ k := by
          rw [(Commute.pow_right (show Commute t c from htc) k).eq]
        _ = c ^ k * (t * q) * t ^ k := by simp only [mul_assoc]
        _ = c ^ k * (c * q * t) * t ^ k := by rw [h1]
        _ = c ^ (k + 1) * q * t ^ (k + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have hj' : t ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have h2 := hkey (2 ^ j)
  rw [hj', one_mul, mul_one] at h2
  have hc2 : c ^ (2 ^ j) = 1 := by
    have : c ^ (2 ^ j) * q = 1 * q := by rw [← h2, one_mul]
    exact mul_right_cancel this
  obtain ⟨m, hm⟩ := hker ⟨c, hcker⟩
  have hcm : c ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ j) (p ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hc1 : c = 1 := by
    have h3 : orderOf c ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hc2
    have h4 : orderOf c ∣ p ^ m := orderOf_dvd_of_pow_eq_one hcm
    have h5 := Nat.dvd_gcd h3 h4
    rw [hcop.gcd_eq_one] at h5
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)
  have h6 : t * q * t⁻¹ * q⁻¹ = 1 := hc1
  calc t * q = t * q * t⁻¹ * q⁻¹ * (q * t) := by group
    _ = q * t := by rw [h6, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
end
