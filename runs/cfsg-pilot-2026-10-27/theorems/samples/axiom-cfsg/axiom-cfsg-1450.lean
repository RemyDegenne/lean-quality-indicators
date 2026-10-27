public section

namespace CFSG.EvenSporadicStandard.HSStd.Transfer

open Subgroup CFSG.Assembly

section Subgroup

variable {H : Type} [Group H] {N A : Subgroup H}

theorem sylow_card_centralizer_subgroupOf [Finite H] (hAN : A ≤ N)
    (hCN : centralizer (A : Set H) ≤ N)
    (hsyl : ∀ S : Sylow 2 (centralizer (A : Set H)), Nat.card S = 2)
    (S : Sylow 2 (centralizer ((A.subgroupOf N : Subgroup N) : Set N))) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : ↥(centralizer ((A.subgroupOf N : Subgroup N) : Set N)) ≃* ↥(centralizer (A : Set H)) :=
    (MulEquiv.subgroupCongr (centralizer_subgroupOf hAN)).trans
      (Subgroup.subgroupOfEquivOfLe hCN)
  have h := hsyl (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S)
  have h2 : Nat.card ↥(Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S) = Nat.card S :=
    Subgroup.card_map_of_injective e.injective
  exact h2.symm.trans h

end Subgroup
end CFSG.EvenSporadicStandard.HSStd.Transfer
end
