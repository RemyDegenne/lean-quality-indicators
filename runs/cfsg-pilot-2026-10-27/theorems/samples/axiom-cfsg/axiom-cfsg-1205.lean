public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.Open CFSG.Blueprint

open CFSG.ABGLocalTools (IsSylowOf)

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem isPGroup_two_sup_zpowers {u v : G} (huv : u * v = v * u) (hu2 : orderOf u = 2)
    (hv2 : orderOf v = 2) : IsPGroup 2 (zpowers u ⊔ zpowers v : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpu : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  have hpv : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hle : zpowers u ≤ centralizer (zpowers v : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro x ⟨k, rfl⟩
    exact (((Commute.zpow_right (show Commute u v from huv) k)).eq).symm
  exact hpu.to_sup_of_normal_right' hpv (hle.trans (centralizer_le_normalizer _))

end CFSG.OddStandard.ChengHeld
end
