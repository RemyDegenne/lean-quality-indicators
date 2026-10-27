public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

variable (S)

theorem nu_O2L1_eq_mul (hhat : ¬ IsHatA6 L)
    (c₁ : ↥(Subgroup.normalizer (V : Set G))) (hc₁ : (c₁ : G) ∈ S.L1) (h3 : (c₁ : G) ^ 3 = 1)
    (hρ : S.frame.ρ c₁ = swap 0 1 * swap 1 2) :
    nu (c₁ : G) (pCoreOf 2 S.L1) =
      (pCoreOf 2 S.L1 ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))).relIndex
        (pCoreOf 2 S.L1) * nu (c₁ : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hQ
  set O := pCoreOf 2 S.L1 with hO
  have hOL1 : O ≤ S.L1 := pCoreOf_le 2 S.L1
  have hL1LT : S.L1 ≤ L ⊔ T := S.L1_le_L.trans le_sup_left
  have hON : O ≤ Subgroup.normalizer (V : Set G) := hOL1.trans (S.L1_le_L.trans S.frame.L_le)
  have hQT : Q ≤ T := S.cLT_le_T hhat
  have hQL1 : Q ≤ Subgroup.normalizer (S.L1 : Set G) := hQT.trans S.T_le_normalizer_L1
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) :=
    hQL1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)
  have hc₁LT : (c₁ : G) ∈ L ⊔ T := hL1LT hc₁
  have hc₁Q : (c₁ : G) ∈ Subgroup.normalizer (Q : Set G) := S.le_normalizer_cLT hc₁LT
  have hc₁O : (c₁ : G) ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 S.L1 hc₁
  have hL1Q : S.L1 ⊓ Q ≤ O := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      (S.h13.sylow.1.to_le (inf_le_right.trans hQT))
    refine A5.le_normalizer_of_forall_conj_mem fun l hl x hx => ⟨?_, ?_⟩
    · exact S.L1.mul_mem (S.L1.mul_mem hl hx.1) (S.L1.inv_mem hl)
    · exact (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_cLT (hL1LT hl)) x).mp hx.2
  set Y := O ⊓ Q with hY
  have hYO : Y ≤ O := inf_le_left
  have hYQ : Y ≤ Q := inf_le_right
  have hY2 : ¬ 3 ∣ Nat.card Y := by
    obtain ⟨e, he⟩ := IsPGroup.iff_card.1 (S.h13.sylow.1.to_le (hYQ.trans hQT))
    rw [he]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hcY : ∀ y ∈ Y, (c₁ : G) * y * (c₁ : G)⁻¹ ∈ Y := fun y hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp hc₁O y).mp hy.1,
      (Subgroup.mem_normalizer_iff.mp hc₁Q y).mp hy.2⟩
  have hνQ : nu (c₁ : G) Q = nu (c₁ : G) Y := by
    have hN : cfix (c₁ : G) Q ≤ Subgroup.normalizer (Y : Set G) := by
      intro q hq
      have hq1 := hQO hq.1
      have hq2 : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq.1
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hq1 y).mp h1,
          (Subgroup.mem_normalizer_iff.mp hq2 y).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hq1 y).mpr h1,
          (Subgroup.mem_normalizer_iff.mp hq2 y).mpr h2⟩
    have hcX : ∀ q ∈ Q, q⁻¹ * ((c₁ : G) * q * (c₁ : G)⁻¹) ∈ Y := by
      intro q hq
      have h1 : q⁻¹ * c₁ * q⁻¹⁻¹ ∈ S.L1 :=
        (Subgroup.mem_normalizer_iff.mp (hQL1 (Q.inv_mem hq)) _).mp hc₁
      have hmem : q⁻¹ * ((c₁ : G) * q * (c₁ : G)⁻¹) ∈ S.L1 ⊓ Q := by
        refine ⟨?_, Q.mul_mem (Q.inv_mem hq) ((Subgroup.mem_normalizer_iff.mp hc₁Q q).mp hq)⟩
        have e : q⁻¹ * ((c₁ : G) * q * (c₁ : G)⁻¹) = (q⁻¹ * c₁ * q⁻¹⁻¹) * (c₁ : G)⁻¹ := by group
        rw [e]
        exact S.L1.mul_mem h1 (S.L1.inv_mem hc₁)
      exact ⟨hL1Q hmem, hmem.2⟩
    rw [nu_mul (c₁ : G) hYQ hN, relIndex_cfix_sup_eq_one h3 hYQ hY2 hcY hcX, one_mul]
  have hN' : cfix (c₁ : G) O ≤ Subgroup.normalizer (Y : Set G) := by
    intro x hx
    have hx1 : x ∈ Subgroup.normalizer (O : Set G) := Subgroup.le_normalizer hx.1
    have hx2 : x ∈ Subgroup.normalizer (Q : Set G) := S.le_normalizer_cLT (hL1LT (hOL1 hx.1))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hx1 y).mp h1,
        (Subgroup.mem_normalizer_iff.mp hx2 y).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hx1 y).mpr h1,
        (Subgroup.mem_normalizer_iff.mp hx2 y).mpr h2⟩
  have hK : ∀ x (hx : x ∈ O), S.frame.ρ ⟨x, hON hx⟩ ∈ K4L := fun x hx =>
    S.rho_O2L1_mem_K4 hx (hON hx)
  have hfp : ∀ x ∈ O, (c₁ : G) * x * (c₁ : G)⁻¹ * x⁻¹ ∈ Y → x ∈ Y := by
    intro x hx h
    have hxN := hON hx
    have h1 : S.frame.ρ (c₁ * ⟨x, hxN⟩ * c₁⁻¹ * (⟨x, hxN⟩)⁻¹) = 1 := (S.rho_eq_one_iff _).2 h.2.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ] at h1
    have h2 : (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x, hxN⟩ * (swap 0 1 * swap 1 2)⁻¹ =
        S.frame.ρ ⟨x, hxN⟩ := by
      calc (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x, hxN⟩ * (swap 0 1 * swap 1 2)⁻¹ =
          (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x, hxN⟩ * (swap 0 1 * swap 1 2)⁻¹ *
            (S.frame.ρ ⟨x, hxN⟩)⁻¹ * S.frame.ρ ⟨x, hxN⟩ := by group
        _ = S.frame.ρ ⟨x, hxN⟩ := by rw [h1, one_mul]
    have h3' := K4L_fix_012 _ (hK x hx) h2
    have hxC := (S.rho_eq_one_iff ⟨x, hxN⟩).1 h3'
    exact ⟨hx, hL1LT (hOL1 hx), hxC⟩
  rw [nu_mul (c₁ : G) hYO hN', cfix_sup_eq_of_fpf hfp, ← hνQ]

end Setting4
end CFSG.Quasithin.H13.A6
end
