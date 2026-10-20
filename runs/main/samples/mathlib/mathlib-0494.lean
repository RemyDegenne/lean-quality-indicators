public section

open Nat Finset

variable {α G M : Type*}

namespace Finset

section Generic

variable [CommMonoid M] {s : Finset α} {a : α} {f : α → M}

@[to_additive]
theorem prod_Ico_reflect (f : ℕ → M) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
    (∏ j ∈ Ico k m, f (n - j)) = ∏ j ∈ Ico (n + 1 - m) (n + 1 - k), f j := by
  have : ∀ i < m, i ≤ n := by
    intro i hi
    exact (add_le_add_iff_right 1).1 (le_trans (Nat.lt_iff_add_one_le.1 hi) h)
  rcases lt_or_ge k m with hkm | hkm
  · rw [← Nat.Ico_image_const_sub_eq_Ico (this _ hkm)]
    refine (prod_image ?_).symm
    simp only [mem_Ico, Set.InjOn, mem_coe]
    rintro i ⟨_, im⟩ j ⟨_, jm⟩ Hij
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)]
  · have : n + 1 - k ≤ n + 1 - m := by
      rw [tsub_le_tsub_iff_left h]
      exact hkm
    simp only [hkm, Ico_eq_empty_of_le, prod_empty, Ico_eq_empty_of_le this]

end Generic
end Finset
end
