namespace OAI

namespace CommonBasesFPRAS

section

section

open scoped RealInnerProductSpace BigOperators Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

open scoped BigOperators Classical

section SamplingObservables

open scoped BigOperators Classical

variable {Γ : Type*} [sectionInstance85 : Fintype Γ] [DecidableEq Γ]

lemma plain_mass_lower (gs : List (Γ × Γ)) (hgs : SlotsFresh gs ∅) (hne : gs≠[])
    (hcover : pairSupport gs=Set.univ) (w : (Γ × Γ) → (Γ × Γ) → ℝ)
    (f : Set Γ → ℝ) (hw : ∀ p r,0 < w p r) (hf : ∀ S,0 < f S)
    (hupper : ∀ p∈gs,∀ r∈gs,p≠r → w p r ≤ 4*slotTotal gs f ∅/slotDefect gs f ∅ p r) :
    1/(5*(gs.length:ℝ)^2) ≤ slotTotal gs f ∅/chainTotal gs w f := by
  have hz := slotTotal_pos gs f hf ∅ hgs
  have hΛ := chainTotal_pos gs hgs hcover w f hf hw
  have hn : (0:ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr hne
  apply (div_le_div_iff₀ (by positivity) hΛ).mpr
  simpa only [one_mul,mul_one,mul_comm] using chainTotal_le gs hgs hne hcover w f hf hupper

end SamplingObservables
end
end
end CommonBasesFPRAS
end OAI
