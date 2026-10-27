public section

namespace CFSG.Quasithin

namespace H

namespace Sz

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree Matrix CFSG.ShultStronglyClosedTI

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open scoped Matrix LinearAlgebra.Projectivization Pointwise

variable {a : ℕ} {K : Type} [Field K]

section Borel

variable [Finite K]

theorem pow_eq_one_of_mem_suzukiB
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {b : suzukiGroup a K}
    (hb : b ∈ suzukiB a K) (hodd : Odd (orderOf b)) : b ^ (2 ^ (2 * a + 1) - 1) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨-, -, hTcard, hTN, -, hBUT, -⟩ := suzuki_borel_structure hK
  have hb' : b ∈ (suzukiU a K : Set (suzukiGroup a K)) * (suzukiT a K : Set (suzukiGroup a K)) := by
    rw [← hBUT]
    exact hb
  obtain ⟨u, hu, t, ht, rfl⟩ := hb'
  have hpow : ∀ k : ℕ, ∃ u' ∈ suzukiU a K, (u * t) ^ k = u' * t ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨u', hu', he⟩ := ih
      refine ⟨u' * (t ^ k * u * (t ^ k)⁻¹), Subgroup.mul_mem _ hu' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTN (Subgroup.pow_mem _ ht k)) u).mp hu
      · rw [pow_succ, he, pow_succ]
        group
  have htq : t ^ (2 ^ (2 * a + 1) - 1) = 1 := by
    rw [← hTcard]
    have h1 : (⟨t, ht⟩ : ↥(suzukiT a K)) ^ Nat.card ↥(suzukiT a K) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  obtain ⟨u', hu', he⟩ := hpow (2 ^ (2 * a + 1) - 1)
  rw [htq, mul_one] at he
  obtain ⟨j, hj⟩ := isPGroup_suzukiU hK ⟨u', hu'⟩
  have hu'j : u' ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf (u * t)) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  have h1 : orderOf ((u * t) ^ (2 ^ (2 * a + 1) - 1)) ∣ orderOf (u * t) := orderOf_pow_dvd _
  have h2 : orderOf ((u * t) ^ (2 ^ (2 * a + 1) - 1)) ∣ 2 ^ j :=
    orderOf_dvd_of_pow_eq_one (by rw [he]; exact hu'j)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end Borel
end Sz
end H
end CFSG.Quasithin
end
