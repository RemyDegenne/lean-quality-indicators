public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin

variable {S : Type} [CommGroup S] {D : FFModel} (hD : D.IsActionModel)

include hD

omit hD in
theorem eq_top_of_card_le {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : Nat.card G ≤ Nat.card H) : H = ⊤ := by
  apply (Subgroup.card_eq_iff_eq_top H).1
  exact le_antisymm (Subgroup.card_le_card_group H) h

end CFSG.QuasithinUnique.B42A57
end
