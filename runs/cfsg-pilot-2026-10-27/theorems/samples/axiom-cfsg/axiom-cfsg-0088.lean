public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.AS76b

open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3 CFSG.Open

variable {G : Type} [Group G]

variable [Finite G]

theorem even_card_oUpperTwoPrime {K : Subgroup G} (hK : Even (Nat.card K)) :
    Even (Nat.card (oUpperTwoPrime K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (even_iff_two_dvd.1 hK)
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : (x : G) ∈ oUpperTwoPrime K :=
    mem_oUpperTwoPrime x.2 (k := 1) (by simpa using congrArg Subtype.val hx2)
  rw [even_iff_two_dvd, ← hx, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk (x : G) hx1]
  exact orderOf_dvd_natCard _

end CFSG.ComponentClassification.Asc76.Sec4
end
