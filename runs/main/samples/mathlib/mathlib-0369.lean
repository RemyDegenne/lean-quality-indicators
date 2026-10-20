@[expose] public section

open Filter Set Function

variable {α β γ ι ι' : Type*}

section MinMax

open Filter

open Finset

@[to_dual]
theorem limsup_finset_sup [ConditionallyCompleteLinearOrder β] [OrderBot β] {f : Filter α}
    {F : ι → α → β} {s : Finset ι}
    (h₁ : ∀ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault)
    (h₂ : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i) := by exact fun _ _ ↦ by isBoundedDefault) :
    limsup (fun a ↦ sup s (fun i ↦ F i a)) f = sup s (fun i ↦ limsup (F i) f) := by
  rcases eq_or_neBot f with (rfl | _)
  · simp [limsup_eq, csInf_univ]
  rcases Finset.eq_empty_or_nonempty s with (rfl | s_nemp)
  · simp only [sup_empty, limsup_const]
  rw [← Finset.sup'_eq_sup s_nemp fun i ↦ limsup (F i) f, ← limsup_finset_sup' s_nemp h₁ h₂]
  congr
  ext a
  exact Eq.symm (Finset.sup'_eq_sup s_nemp (fun i ↦ F i a))

end MinMax
end
