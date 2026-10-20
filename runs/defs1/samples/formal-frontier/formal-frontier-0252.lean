@[expose] public section

universe u v

namespace Subgroup

variable {G : Type u} [Group G]

/-- Index-two subgroups correspond to nontrivial characters to the two-element group. -/
noncomputable def indexTwoEquivNontrivialHom :
    {H : Subgroup G // H.index = 2} ≃
      {χ : G →* Multiplicative (ZMod 2) // χ ≠ 1} where
  toFun H := ⟨H.val.characterOfIndexTwo H.property,
    H.val.characterOfIndexTwo_ne_one H.property⟩
  invFun χ := ⟨χ.val.ker,
    (MonoidHom.ker_index_eq_two_iff (by simp [Nat.card_eq_fintype_card]) χ.val).mpr
      χ.property⟩
  left_inv H := Subtype.ext (H.val.ker_characterOfIndexTwo H.property)
  right_inv χ := by
    apply Subtype.ext
    symm
    exact χ.val.ker.characterOfIndexTwo_unique
      ((MonoidHom.ker_index_eq_two_iff (by simp [Nat.card_eq_fintype_card]) χ.val).mpr
        χ.property) χ.val rfl

end Subgroup
end
