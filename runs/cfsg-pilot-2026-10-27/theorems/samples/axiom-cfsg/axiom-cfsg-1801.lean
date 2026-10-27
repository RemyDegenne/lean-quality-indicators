public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Orders2

variable {G : Type*} [Group G]

theorem card_eq_mul_of_relIndex {S T : Subgroup G} (hST : S ≤ T) :
    Nat.card T = Nat.card S * S.relIndex T := by
  have := Subgroup.card_mul_index (S.subgroupOf T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv] at this
  exact this.symm

end Orders2
end CFSG.QuasithinUnique.Lin2
end
