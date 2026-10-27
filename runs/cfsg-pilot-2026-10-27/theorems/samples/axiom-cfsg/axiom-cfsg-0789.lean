public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

theorem dew1_prime_dvd_centralizer {Ω : Set (Subgroup G)} (h : DEHyp Ω)
    (h4 : ∀ K ∈ Ω, (twinSet Ω K).ncard = 4) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card ↥(Subgroup.centralizer (zGroup Ω : Set G))) : p = 2 ∨ p = 3 := by
  by_contra hne
  have h4' : p ≠ 4 := by rintro rfl; norm_num at hp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hxp : (c : G) ^ p = 1 := by
    have h1 := pow_orderOf_eq_one c
    rw [hc] at h1
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have hord : orderOf (c : G) = p := (Subgroup.orderOf_coe c).trans hc
  have h1 := dew1_no_big_prime h h4 c.2 hp h5 hxp
  rw [h1, orderOf_one] at hord
  exact hp.one_lt.ne' hord.symm

end CFSG.ClassicalInvolution.Q3.Sec13
end
