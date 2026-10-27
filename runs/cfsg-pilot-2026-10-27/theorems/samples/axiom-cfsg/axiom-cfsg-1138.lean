attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

open Matrix

open Sp6Over (GL6 M6 V7)

variable {G : Type} [Group G] [Finite G]

namespace S57

theorem frattini {C K : Type*} [Group C] [Finite C] [Group K] (ψ : C →* K)
    (hker : IsPGroup 2 ψ.ker) {u : C} (hu : orderOf u = 3) {g : C}
    (hg : ψ g * ψ u = ψ u * ψ g) : ∃ d : C, d * u = u * d ∧ ψ d = ψ g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk3 : ∀ y : C, ψ y = 1 → y ^ 3 = 1 → y = 1 := by
    intro y hy h3
    obtain ⟨n, hn⟩ := hker ⟨y, hy⟩
    have h1 : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hd : orderOf y ∣ Nat.gcd (2 ^ n) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h3)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n (by norm_num))] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : ψ u ≠ 1 := fun h => by
    have := hk3 u h hu3
    rw [this, orderOf_one] at hu
    omega
  have hψu : orderOf (ψ u) = 3 := orderOf_eq_prime (by rw [← map_pow, hu3, map_one]) hu1
  set N := (Subgroup.zpowers (ψ u)).comap ψ with hN
  have huN : u ∈ N := Subgroup.mem_zpowers _
  set x := g * u * g⁻¹ with hx
  have hψx : ψ x = ψ u := by rw [hx, map_mul, map_mul, hg, map_inv, mul_inv_cancel_right]
  have hxN : x ∈ N := by
    change ψ x ∈ Subgroup.zpowers (ψ u)
    rw [hψx]; exact Subgroup.mem_zpowers _
  set ψN := ψ.comp N.subtype with hψN
  have hkerN : IsPGroup 2 ψN.ker := fun k => by
    obtain ⟨n, hn⟩ := hker ⟨((k : N) : C), k.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hkerN
  have hrange : ψN.range = Subgroup.zpowers (ψ u) := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨⟨u, huN⟩, rfl⟩)
    rintro _ ⟨k, rfl⟩
    exact k.2
  have hNc : Nat.card N = 2 ^ n * 3 := by
    rw [← Subgroup.card_ker_mul_card_range ψN, hn, hrange, Nat.card_zpowers, hψu]
  have hsyl : ∀ y : N, orderOf y = 3 →
      ∃ P : Sylow 3 N, (P : Subgroup N) = Subgroup.zpowers y := by
    intro y hy
    have hP : IsPGroup 3 (Subgroup.zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
    have hidx : ¬ 3 ∣ (Subgroup.zpowers y).index := by
      have h := (Subgroup.zpowers y).index_mul_card
      rw [Nat.card_zpowers, hy, hNc] at h
      have h' : (Subgroup.zpowers y).index = 2 ^ n := by omega
      rw [h']
      exact fun h3 => by
        have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
        omega
    exact ⟨hP.toSylow hidx, IsPGroup.toSylow_coe hP hidx⟩
  have hoN : orderOf (⟨u, huN⟩ : N) = 3 := by rw [Subgroup.orderOf_mk, hu]
  have hoX : orderOf (⟨x, hxN⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    change orderOf ((MulAut.conj g).toMonoidHom u) = 3
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u).trans hu
  obtain ⟨P, hP⟩ := hsyl _ hoN
  obtain ⟨Q, hQ⟩ := hsyl _ hoX
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq N Q P
  have hmx : m * ⟨x, hxN⟩ * m⁻¹ ∈ Subgroup.zpowers (⟨u, huN⟩ : N) := by
    rw [← hP, ← hm, Sylow.coe_subgroup_smul]
    have : (⟨x, hxN⟩ : N) ∈ (Q : Subgroup N) := by rw [hQ]; exact Subgroup.mem_zpowers _
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj m) _ this
    simpa [MulAut.smul_def, MulAut.conj_apply] using h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmx
  have hk' : u ^ k = (m : C) * x * (m : C)⁻¹ := by
    simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (m.2 : ψ (m : C) ∈ Subgroup.zpowers (ψ u))
  set d₀ := (m : C) * g with hd₀
  have hcomm : ψ (m : C) * ψ u = ψ u * ψ (m : C) := by
    rw [← hj]; exact (Commute.zpow_self (ψ u) j).eq
  have hd₀u : d₀ * u * d₀⁻¹ = u := by
    have h1 : d₀ * u * d₀⁻¹ = u ^ k := by rw [hk', hd₀, hx]; group
    have e1 : ψ (d₀ * u * d₀⁻¹) = ψ u := by
      have : ψ (d₀ * u * d₀⁻¹) = ψ (m : C) * (ψ g * ψ u) * (ψ g)⁻¹ * (ψ (m : C))⁻¹ := by
        rw [hd₀]; simp only [map_mul, map_inv, _root_.mul_inv_rev]; group
      rw [this, hg, ← mul_assoc, hcomm]; group
    have h2 : ψ (u ^ (k - 1)) = 1 := by
      rw [_root_.zpow_sub_one, map_mul, map_inv, ← h1, e1, mul_inv_cancel]
    have h3 : (u ^ (k - 1)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hu3,
        _root_.one_zpow]
    have h4 := hk3 _ h2 h3
    rw [h1, show k = (k - 1) + 1 by ring, _root_.zpow_add_one, h4, one_mul]
  refine ⟨u ^ (-j) * d₀, ?_, ?_⟩
  · have hd : d₀ * u = u * d₀ := by
      calc d₀ * u = d₀ * u * d₀⁻¹ * d₀ := by group
        _ = u * d₀ := by rw [hd₀u]
    calc u ^ (-j) * d₀ * u = u ^ (-j) * (u * d₀) := by rw [mul_assoc, hd]
      _ = u * (u ^ (-j) * d₀) := by
        simp only [← mul_assoc, (Commute.zpow_self u (-j)).eq]
  · rw [map_mul, map_zpow, hd₀, map_mul, ← mul_assoc, ← hj, ← _root_.zpow_add, neg_add_cancel,
      zpow_zero, one_mul]

end S57
end CFSG.RankThree.PartTwo.Sec21.FF81
end
