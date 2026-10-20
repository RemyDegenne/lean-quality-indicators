@[expose] public section

open MeasurableSpace Set

open scoped MeasureTheory

variable {α β : Type*}

theorem mem_generatePiSystem_iUnion_elim {α β} {g : β → Set (Set α)} (h_pi : ∀ b, IsPiSystem (g b))
    (t : Set α) (h_t : t ∈ generatePiSystem (⋃ b, g b)) :
    ∃ (T : Finset β) (f : β → Set α), (t = ⋂ b ∈ T, f b) ∧ ∀ b ∈ T, f b ∈ g b := by
  classical
  induction h_t using generatePiSystem_induction with
  | base s h_s =>
    rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩
    refine ⟨{b}, fun _ => s, ?_⟩
    simpa using h_s_in_t'
  | inter _ _ h_gen_s h_gen_t' h_nonempty h_s h_t' =>
    rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩⟩⟩
    use T_s ∪ T_t', fun b : β =>
      if b ∈ T_s then if b ∈ T_t' then f_s b ∩ f_t' b else f_s b
      else if b ∈ T_t' then f_t' b else (∅ : Set α)
    constructor
    · ext a
      simp_rw [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
      grind
    intro b h_b
    split_ifs with hbs hbt hbt
    · refine h_pi b (f_s b) (h_s b hbs) (f_t' b) (h_t' b hbt) (Set.Nonempty.mono ?_ h_nonempty)
      exact Set.inter_subset_inter (Set.biInter_subset_of_mem hbs) (Set.biInter_subset_of_mem hbt)
    · exact h_s b hbs
    · exact h_t' b hbt
    · rw [Finset.mem_union] at h_b
      apply False.elim (h_b.elim hbs hbt)

end
