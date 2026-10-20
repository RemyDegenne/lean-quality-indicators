public section

noncomputable section

namespace TauCeti

section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f : E → EReal} {x : E} {y : F} {r : ℝ}

theorem mem_subdifferential_iff_add_fenchelConjugate_eq :
    y ∈ subdifferential B f x ↔ f x + fenchelConjugate B f y = (B x y : EReal) := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
      ⟨(f x).toReal, (EReal.coe_toReal (ne_top_of_mem_subdifferential B h)
        (ne_bot_of_mem_subdifferential B h)).symm⟩
    rw [fenchelConjugate_eq_of_mem_subdifferential B h, hr, ← EReal.coe_sub, ← EReal.coe_add,
      add_sub_cancel]
  · intro h
    have hbot : f x ≠ ⊥ := fun hx => by
      rw [hx, EReal.bot_add] at h
      exact EReal.coe_ne_bot _ h.symm
    have htop : f x ≠ ⊤ := fun hx => by
      rw [hx] at h
      rcases eq_or_ne (fenchelConjugate B f y) ⊥ with hy | hy
      · rw [hy, EReal.add_bot] at h
        exact EReal.coe_ne_bot _ h.symm
      · rw [EReal.top_add_of_ne_bot hy] at h
        exact EReal.coe_ne_top _ h.symm
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
    have hF : fenchelConjugate B f y = ((B x y - r : ℝ) : EReal) := by
      rw [hr] at h
      rw [EReal.coe_sub, ← h, EReal.add_sub_cancel_left]
    exact (mem_subdifferential_iff_forall_sub_le B hr).2 fun x' =>
      hF ▸ sub_le_fenchelConjugate B f x' y

end
end TauCeti
end
end
