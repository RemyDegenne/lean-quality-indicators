universe u

open Ordinal

public noncomputable section

namespace NatOrdinal

variable {t e : NatOrdinal.{u}}

variable {O t₁ t₂ e₁ e₂ : NatOrdinal.{u}}

@[blueprint "lem:two-lowerings-have-strict-bound"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Uniform bound for simultaneous decreases in a Hessenberg sum")
  (statement := )
  (proof := )]
theorem exists_lt_forall_add_add_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e₁) (he₂ : leastTerm t₂ = ω^ e₂) :
    ∃ B, B < O + t₁ + t₂ ∧ ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ B := by
  rcases le_total e₁ e₂ with h | h
  · exact exists_lt_forall_add_add_le_of_le ht₁ ht₂ he₁ he₂ h
  · obtain ⟨B, hB, hall⟩ := exists_lt_forall_add_add_le_of_le (O := O) ht₂ ht₁ he₂ he₁ h
    refine ⟨B, by rwa [add_right_comm] at hB, fun ρ₁ ρ₂ hρ₁ hρ₂ ↦ ?_⟩
    rw [add_right_comm]
    exact hall ρ₂ ρ₁ hρ₂ hρ₁

end NatOrdinal
end
