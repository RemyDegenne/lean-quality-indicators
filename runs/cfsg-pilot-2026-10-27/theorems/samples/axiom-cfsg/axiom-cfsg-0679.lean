public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem iThm32
    (h : NearAsolvAction p A X) {X₁ X₂ : Subgroup Γ}
    (hP : (X₁, X₂) ∈ iPairsY A X Y) :
    ∃ Z₁ Z₂ : Subgroup Γ, Z₁ ≤ X₁ ∧ Z₂ ≤ X₂ ∧ (Z₁, Z₂) ∈ iPairsY A X Y ∧
      Group.IsSolvable Z₂ ∧ CyclicMod A (secCenIn A Z₁ Z₂) := by
  obtain ⟨W₁, W₂, hW₁, hW₂, hW, hW₂s⟩ := Thm32.exists_solvable_of_pair h hP
  obtain ⟨B, hBA, ⟨a, ha, hle⟩, hpair⟩ := Thm32.exists_cen_pair h hW
  have hA₁ : A ≤ Subgroup.normalizer (W₁ : Set Γ) :=
    le_sup_right.trans (Thm32.isDAIn_left_of_mem_iPairsY hW).2
  have hA₂ : A ≤ Subgroup.normalizer (W₂ : Set Γ) :=
    le_sup_right.trans (Thm32.isDAIn_right_of_mem_iPairsY hW).2
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := h.elemAbelian.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  exact ⟨cenIn W₁ (B : Set Γ), cenIn W₂ (B : Set Γ), inf_le_left.trans hW₁,
    inf_le_left.trans hW₂, hpair, Thm211.isSolvable_of_le inf_le_left hW₂s, a, ha,
    hle.trans (sup_le_sup_right (Thm32.le_secCenIn_cen hBA hcomm hA₁ hA₂) _)⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
end
