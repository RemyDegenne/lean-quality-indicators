public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)

include S

theorem kAct_ne_one {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) {x : G} (hx : x ∈ Lp)
    (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) : kAct K ⟨x, hD.Lp_K hx⟩ ≠ 1 := by
  intro h
  have hQ := S.mem_pCoreOf_of_kAct_eq_one hD hx h
  obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 Lp ⟨x, hQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hxo)
  exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd))

end Set14
end CFSG.Quasithin.H13.U3
end
