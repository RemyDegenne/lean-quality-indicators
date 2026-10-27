public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

variable {G : Type*} [Group G]

theorem pCoreOf_le_centralizer614 [Finite G] {T : Subgroup G} {y : G} (hy : orderOf y = 5)
    (hTy : T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    pCoreOf 2 (Subgroup.zpowers y ⊔ T) ≤ Subgroup.centralizer ({y} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro o ho
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hoXT : o ∈ Subgroup.zpowers y ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ho
  have hO2 : IsPGroup 2 (pCoreOf 2 (Subgroup.zpowers y ⊔ T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXN : Subgroup.zpowers y ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    sup_le Subgroup.le_normalizer hTy
  set c := o * y * o⁻¹ * y⁻¹ with hc
  have hc1 : c ∈ Subgroup.zpowers y := by
    have h := (Subgroup.mem_normalizer_iff.mp (hXN hoXT) y).mp (Subgroup.mem_zpowers y)
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  have hc2 : c ∈ pCoreOf 2 (Subgroup.zpowers y ⊔ T) := by
    have hy' : y ∈ Subgroup.zpowers y ⊔ T :=
      (le_sup_left : Subgroup.zpowers y ≤ Subgroup.zpowers y ⊔ T) (Subgroup.mem_zpowers y)
    have h := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hy') o⁻¹).mp
      (Subgroup.inv_mem _ ho)
    have e : c = o * (y * o⁻¹ * y⁻¹) := by rw [hc]; group
    rw [e]
    exact Subgroup.mul_mem _ ho h
  have hc3 : c = 1 := by
    obtain ⟨k, hk⟩ := hO2 ⟨c, hc2⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h5 : c ^ 5 = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy,
        pow_orderOf_eq_one, one_zpow]
    have hd1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left _ (by norm_num)
    have : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact orderOf_eq_one_iff.mp this
  have e : o * y = y * o := by
    calc o * y = c * (y * o) := by rw [hc]; group
      _ = y * o := by rw [hc3, one_mul]
  exact e

end
end CFSG.Quasithin.H13
end
