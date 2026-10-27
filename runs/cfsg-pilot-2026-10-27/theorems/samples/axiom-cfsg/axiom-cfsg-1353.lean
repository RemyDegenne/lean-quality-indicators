public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Fischer CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

open scoped Pointwise

namespace Sec3Mod

open Census SHatClosed

section Census

theorem card_le_sixteen {E : Subgroup OV} (hEL : E ≤ Lc) (hsq : ∀ x ∈ E, x * x = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 16 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨a, b, c, d, h4, haE, hbE, hcE, hdE⟩ := exists_indep4 hEL hsq hcomm (by omega)
  set Y := (Set.toFinite {x : MulAction.stabilizer OV N0 | (x : OV) ∈ E ∧ x ≠ 1}).toFinset
    with hY
  have hX := card_comm_le h4 Y fun x hx => by
    rw [hY, Set.Finite.mem_toFinset] at hx
    have hxE := hx.1
    refine ⟨hEL hxE, Subtype.ext (hsq _ hxE), hx.2, Subtype.ext (hcomm _ hxE _ haE),
      Subtype.ext (hcomm _ hxE _ hbE), Subtype.ext (hcomm _ hxE _ hcE),
      Subtype.ext (hcomm _ hxE _ hdE)⟩
  obtain ⟨x, hxE, hxY⟩ := exists_mem_not_mem (E := E) (insert 1 (Y.image Subtype.val))
    (lt_of_le_of_lt (Finset.card_insert_le _ _)
      (lt_of_le_of_lt (Nat.succ_le_succ (Finset.card_image_le.trans hX)) (by omega)))
  apply hxY
  rw [Finset.mem_insert, Finset.mem_image]
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · refine Or.inr ⟨⟨x, Lc_le_stab (hEL hxE)⟩, ?_, rfl⟩
    rw [hY, Set.Finite.mem_toFinset]
    exact ⟨hxE, fun h => hx1 (congrArg Subtype.val h)⟩

end Census
end Sec3Mod
end CFSG.ComponentClassification.AS81
end
