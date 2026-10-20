public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V]

theorem card_path_eq_ite_add_sum_firstArrow [DecidableEq V] [Fintype V] (a : V)
    [∀ b : V, Finite (a ⟶ b)] (j : V) [∀ b : V, Finite (Quiver.Path b j)] :
    Nat.card (Quiver.Path a j)
      = (if a = j then 1 else 0)
        + ∑ b : V, Nat.card (a ⟶ b) * Nat.card (Quiver.Path b j) := by
  have hsub : Subsingleton (PLift (a = j)) := ⟨fun x y ↦ by cases x; cases y; rfl⟩
  have : Finite (PLift (a = j)) := Finite.of_subsingleton
  have hcard : Nat.card (PLift (a = j)) = if a = j then 1 else 0 := by
    by_cases h : a = j
    · rw [ite_eq_left h]
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨h⟩⟩⟩
    · rw [ite_eq_right h]
      have : IsEmpty (PLift (a = j)) := ⟨fun x ↦ h x.down⟩
      exact Nat.card_of_isEmpty
  rw [Nat.card_congr (pathFirstArrowEquiv a j), Nat.card_sum, hcard, Nat.card_sigma]
  exact congrArg _ (Finset.sum_congr rfl fun b _ ↦ Nat.card_prod _ _)

end TauCeti
end
