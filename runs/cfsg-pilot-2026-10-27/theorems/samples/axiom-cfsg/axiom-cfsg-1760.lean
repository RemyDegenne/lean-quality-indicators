public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem two_lt_card_inf {S : Subgroup G} (hin : centralizer ({t} : Set G) = L ⊔ zpowers t)
    (htL : t ∈ centralizer (L : Set G)) (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (ht2 : orderOf t = 2) (hle : S ≤ centralizer ({t} : Set G)) (h2 : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) (hL4 : 4 ∣ Nat.card L) :
    2 < Nat.card (S ⊓ L : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := card_sup_zpowers htL hLC ht2
  rw [← hin] at hC
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  have hSC := relIndex_mul_card (H := S) (K := centralizer ({t} : Set G))
  rw [inf_of_le_left hle, hk, hC] at hSC
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have hk3' : k < 3 := Nat.lt_of_not_le hk3
    obtain ⟨m, hm⟩ := hL4
    interval_cases k <;> omega
  have hLC2 : L.relIndex (centralizer ({t} : Set G)) = 2 := by
    have h := relIndex_mul_card (H := L) (K := centralizer ({t} : Set G))
    have hLle : L ≤ centralizer ({t} : Set G) := hin ▸ le_sup_left
    rw [inf_of_le_left hLle, hC] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hrel : L.relIndex S ≤ 2 := by
    rw [← hLC2]
    exact relIndex_le_of_le_right hle (by rw [hLC2]; norm_num)
  have h3 := relIndex_mul_card (H := L) (K := S)
  rw [inf_comm, hk] at h3
  have hpow : 8 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk3)
  by_contra hle2
  have hle2' : Nat.card (S ⊓ L : Subgroup G) ≤ 2 := Nat.le_of_not_lt hle2
  have : L.relIndex S * Nat.card (S ⊓ L : Subgroup G) ≤ 2 * 2 :=
    Nat.mul_le_mul hrel hle2'
  omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
end
