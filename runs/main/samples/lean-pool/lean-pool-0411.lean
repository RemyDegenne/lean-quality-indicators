@[expose] public section

open Finset

namespace Erdos865

theorem card_A_bound {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Finset.Icc 1 N) (h : ℕ) :
    A.card ≤ (Xset A h).card + (Yset A N h).card + 2 + (N - 2 * h) := by
  -- Let's show that $A$ is a subset of
  -- $Xset A h ∪ (Yset A N h).image (fun r => h + r) ∪ {h, 2*h} ∪ Finset.Icc (2*h + 1) N$.
  have h_subset : A ⊆ Xset A h ∪ (Yset A N h).image (fun r => h + r) ∪ {h, 2 * h} ∪
      Finset.Icc (2 * h + 1) N := by
    intro a ha; by_cases ha1 : a < h <;> by_cases ha2 : a = h <;> by_cases ha3 : a = 2 * h <;>
      simp_all +decide only [subset_iff, mem_Icc, lt_self_iff_false, not_lt, not_false_eq_true,
        mem_singleton, insert_eq_of_mem, union_insert, union_assoc, union_singleton, insert_union,
        mem_insert, mem_union, mem_image, Nat.add_eq_left, exists_eq_right, add_le_iff_nonpos_right,
        Order.add_one_le_iff, and_true, or_false, false_or, true_or, or_true];
    · exact Or.inl <|
        Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by linarith [ hsub ha ], ha1 ⟩, ha ⟩;
    · by_cases ha4 : a < 2 * h <;>
        simp_all +decide only [not_lt, Xset, mem_filter, mem_Ico, true_and, and_true, Yset];
      · exact Or.inr <| Or.inl
          ⟨ a - h, ⟨ ⟨ Nat.sub_pos_of_lt <| lt_of_le_of_ne ha1 <| Ne.symm ha2, by omega ⟩,
            by linarith [ hsub ha, Nat.sub_add_cancel ha1 ], by convert ha using 1; omega ⟩,
            by omega ⟩;
      · exact Or.inr <| Or.inr <| lt_of_le_of_ne ha4 <| Ne.symm ha3;
  refine le_trans ( Finset.card_le_card h_subset ) ?_;
  refine le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ )
    ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add
      ( Finset.card_le_card ( Finset.Subset.refl _ ) ) ( Finset.card_image_le ) ) )
      ( Finset.card_insert_le _ _ ) ) ) ( by simp +arith +decide [ Nat.card_Icc ] ) )

end Erdos865
end
