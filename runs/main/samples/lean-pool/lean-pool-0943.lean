@[expose] public section

namespace KaltonRoberts

open Finset BigOperators

theorem card_perm_constrained_step (n s t : ℕ) (hs : s < t) (ht : t ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ (i : Fin n), i.val < s + 1 → (σ i).val < t} * (n - s) =
    Fintype.card {σ : Equiv.Perm (Fin n) //
      ∀ (i : Fin n), i.val < s → (σ i).val < t} * (t - s) := by
  rw [ Fintype.card_subtype, Fintype.card_subtype ];
  have h_card_perm : (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ
    i).val < t) Finset.univ).card * (t - s) =
    (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s + 1 → (σ i).val < t)
      Finset.univ).card * (n - s) := by
    have h_available_card : ∀ σ : Equiv.Perm (Fin n), (∀ i : Fin n, i.val < s → (σ i).val < t) →
      (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val < t) Finset.univ).card = t - s := by
        intro σ hσ
        have h_card_perm_aux : (Finset.filter (fun i : Fin n => (σ i).val < t) Finset.univ).card = t
          := by
          have h_card_perm_aux : (Finset.filter (fun i : Fin n => (i : ℕ) < t) Finset.univ).card = t
            := by
            rw [ Finset.card_eq_of_bijective ];
            · use fun i hi => ⟨ i, by linarith ⟩;
            · grind;
            · grind;
            · aesop;
          convert h_card_perm_aux using 1;
          rw [ Finset.card_filter, Finset.card_filter ];
          conv_rhs => rw [ ← Equiv.sum_comp σ ];
        have h_card_perm_aux : (Finset.filter (fun i : Fin n => i.val < s ∧ (σ i).val < t)
          Finset.univ).card = s := by
          rw [
            show
              Finset.filter
                  (fun i : Fin n => (i : ℕ) < s ∧ (σ i : ℕ) < t) Finset.univ =
                Finset.Iio ⟨s, by linarith⟩ from
              Finset.ext fun x => by aesop]
          aesop
        have h_card_perm_aux : (Finset.filter (fun i : Fin n => (σ i).val < t) Finset.univ).card =
          (Finset.filter (fun i : Fin n => i.val < s ∧ (σ i).val < t) Finset.univ).card +
            (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val < t) Finset.univ).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · congr with i; by_cases hi : ( i : ℕ ) < s <;> aesop;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
        exact eq_tsub_of_add_eq ( by linarith )
    have h_first_sum : (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ
      i).val < t) Finset.univ).card * (t - s) =
      (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ i).val < t)
        Finset.univ).sum (fun σ => (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val < t)
          Finset.univ).card) := by
        rw [ Finset.sum_congr rfl fun x hx => h_available_card x <| Finset.mem_filter.mp hx |>.2 ];
          aesop;
    have h_double_count : (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ i : Fin n, i.val < s → (σ
      i).val < t) Finset.univ).sum (fun σ => (Finset.filter (fun i : Fin n => i.val ≥ s ∧ (σ i).val
        < t) Finset.univ).card) =
      (Finset.filter (fun i : Fin n => i.val ≥ s) Finset.univ).sum (fun i => (Finset.filter (fun σ :
        Equiv.Perm (Fin n) => (σ i).val < t ∧ ∀ j : Fin n, j.val < s → (σ j).val < t)
          Finset.univ).card) := by
        simp +decide only [card_filter];
        rw [ Finset.sum_comm ];
        rw [ Finset.sum_filter ];
        congr with i
        by_cases hi : ( i : ℕ ) ≥ s
        · simp +decide only [hi, sum_boole, Nat.cast_id, true_and, ite_true]
          exact congr_arg Finset.card ( by ext; aesop )
        · simp +decide only [hi, sum_boole, Nat.cast_id, false_and, ite_false,
            Finset.sum_const_zero]
    have h_swap_card : ∀ i : Fin n, i.val ≥ s → (Finset.filter (fun σ : Equiv.Perm (Fin n) => (σ
      i).val < t ∧ ∀ j : Fin n, j.val < s → (σ j).val < t) Finset.univ).card =
      (Finset.filter (fun σ : Equiv.Perm (Fin n) => ∀ j : Fin n, j.val < s + 1 → (σ j).val < t)
        Finset.univ).card := by
        intro i hi
        let k : Fin n := ⟨s, by linarith [Fin.is_lt i]⟩
        have hk_value : (k : ℕ) = s := rfl
        apply Finset.card_bij (fun σ _ => σ * Equiv.swap i k);
        · intro σ hσ
          rw [Finset.mem_filter] at hσ
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro j hj
          by_cases hj_boundary : j = k
          · subst j
            simpa [Equiv.swap_apply_def, k] using hσ.2.1
          · have hj_small : (j : ℕ) < s := by
              have hj_ne : (j : ℕ) ≠ s := by
                intro h
                exact hj_boundary (Fin.ext (by simpa [hk_value] using h))
              omega
            have hji : j ≠ i := by
              intro h
              have h_value : (j : ℕ) = (i : ℕ) :=
                congrArg (fun x : Fin n => (x : ℕ)) h
              omega
            simpa [Equiv.swap_apply_def, hji, hj_boundary] using hσ.2.2 j hj_small
        · aesop;
        · intro σ hσ
          use σ * Equiv.swap i k
          rw [Finset.mem_filter] at hσ
          refine ⟨?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            constructor
            · have hk_lt : (k : ℕ) < s + 1 := by omega
              simpa [Equiv.swap_apply_def, k] using hσ.2 k hk_lt
            · intro j hj_small
              have hji : j ≠ i := by
                intro h
                have h_value : (j : ℕ) = (i : ℕ) :=
                  congrArg (fun x : Fin n => (x : ℕ)) h
                omega
              have hjk : j ≠ k := by
                intro h
                have h_value : (j : ℕ) = s := by
                  simpa [hk_value] using congrArg (fun x : Fin n => (x : ℕ)) h
                omega
              have hj_succ : (j : ℕ) < s + 1 := by omega
              simpa [Equiv.swap_apply_def, hji, hjk] using hσ.2 j hj_succ
          · simp [mul_assoc]
    rw [h_first_sum, h_double_count]
    rw [Finset.sum_congr rfl fun x hx => h_swap_card x <| Finset.mem_filter.mp hx |>.2]
    rw [show (Finset.univ.filter fun x : Fin n => s ≤ (x : ℕ)) =
        Finset.Ici ⟨s, by linarith⟩ by
      ext x
      simp [Fin.le_def]]
    simp [Nat.mul_comm]
  exact h_card_perm.symm

end KaltonRoberts
end
