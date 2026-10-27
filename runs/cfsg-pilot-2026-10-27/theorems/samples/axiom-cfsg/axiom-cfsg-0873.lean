public section

namespace CFSG.LieType.Steinberg

open scoped commutatorElement

universe u v

theorem le_center_of_height_max {G : Type u} [Group G] {ι : Type v} (h : ι → ℤ)
    (A : ι → Subgroup G) (hab : ∀ i, IsMulCommutative (A i)) (hgen : ⨆ i, A i = ⊤)
    (hc : ∀ i j, i ≠ j → ⁅A i, A j⁆ ≤ ⨆ (k) (_ : max (h i) (h j) < h k), A k) {m : ℤ}
    (hle : ∀ i, h i ≤ m) {k : ι} (hk : h k = m) : A k ≤ Subgroup.center G := by
  have hj : ∀ j, A j ≤ Subgroup.centralizer (A k : Set G) := fun j => by
    by_cases hjk : j = k
    · subst hjk
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := (hab j).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
      exact congrArg Subtype.val this
    · have hbot : ⁅A j, A k⁆ = ⊥ := by
        refine eq_bot_iff.2 ((hc j k hjk).trans (iSup₂_le fun l hl => ?_))
        exact absurd (lt_of_le_of_lt (le_max_right _ _) hl) (by rw [hk]; exact not_lt.2 (hle l))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ Subgroup.centralizer (A k : Set G) := by
    have : (⊤ : Subgroup G) ≤ Subgroup.centralizer (A k : Set G) := hgen ▸ iSup_le hj
    exact this (Subgroup.mem_top y)
  exact (Subgroup.mem_centralizer_iff.1 hy x hx).symm

end CFSG.LieType.Steinberg
end
