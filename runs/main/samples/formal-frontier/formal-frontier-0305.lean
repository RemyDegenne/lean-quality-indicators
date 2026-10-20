@[expose] public section

universe u v

namespace FreeGroupBasis

variable {ι : Type u} {G : Type v} [Group G]

theorem natCard_eq_rank (b : FreeGroupBasis ι G) [Group.FG G] :
    Nat.card ι = Group.rank G := by
  classical
  let _ : Finite ι := b.finite
  let _ : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · -- A generating set determines every homomorphism into the two-element group.
    obtain ⟨s, hs, hgen⟩ := Group.rank_spec G
    have hc2 : Nat.card (Multiplicative (ZMod 2)) = 2 :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)
    have hcount := Nat.card_le_card_of_injective _
      (lift_restrict_injective (K := Multiplicative (ZMod 2)) b hgen)
    rw [Nat.card_fun, Nat.card_fun, hc2, Nat.card_eq_finsetCard, hs] at hcount
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcount
  · -- The basis itself generates the group, giving the opposite inequality.
    have hlift : FreeGroup.lift (b : ι → G) = b.repr.symm.toMonoidHom := by
      ext i
      apply b.repr.injective
      simp
    have hgen : Subgroup.closure (Set.range b) = ⊤ := by
      apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mp
      rw [hlift]
      exact b.repr.symm.surjective
    have hupper : Group.rank G ≤ (Finset.univ.image b).card :=
      Group.rank_le (by simpa using hgen)
    exact hupper.trans (Finset.card_image_le.trans_eq (by simp [Nat.card_eq_fintype_card]))

end FreeGroupBasis
end
