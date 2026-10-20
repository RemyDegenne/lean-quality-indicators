@[expose] public section

lemma Real.exists_eq_of_iSup_eq_of_finite_domain {ι : Type*} {f : ι → ℝ} {a : ℝ}
    [Finite ι] (hfz : ∃ i, f i ≥ 0) (hf : ⨆ i, f i = a) : ∃ i, f i = a := by
  have : Nonempty ι := hfz.nonempty
  have iSup_lt_iff : ⨆ i ∈ (Set.univ : Set ι), f i < a ↔ ∀ i ∈ Set.univ, f i < a := by
    apply Set.Finite.ciSup_lt_iff Set.finite_univ
    simp_all
  have lt_iSup_iff : a < ⨆ i, f i ↔ ∃ i, a < f i :=
    lt_ciSup_iff (range_bddAbove_of_finite_domain f)
  by_contra nex; simp only [not_exists] at nex
  have : ∀ (i : ι), f i < a := fun i ↦ by
    obtain h | h | h := lt_trichotomy (f i) a
    · exact h
    · exfalso; exact nex i h
    · exfalso; exact ne_of_lt (lt_iSup_iff.mpr ⟨i, h⟩) hf.symm
  simp_all

end
