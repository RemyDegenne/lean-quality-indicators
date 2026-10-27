public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SplitC

open CFSG.EvenSmallLie.OmegaEight.CPrime

variable {G : Type} [Group G] {t : G} {L : Subgroup G}

theorem mem_of_isPGroup_of_odd {K M V : Subgroup G} (hn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hodd : Odd (K.relIndex M)) (hV : IsPGroup 2 V) {x : G} (hxV : x ∈ V) (hxM : x ∈ M) :
    x ∈ K := by
  obtain ⟨k, hk⟩ := hV ⟨x, hxV⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine mem_of_coprime_relIndex hn hxM ?_
  exact (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)).coprime_dvd_right
    (orderOf_dvd_of_pow_eq_one hk')

end CFSG.EvenSmallLie.OmegaEight.Stage0
end
