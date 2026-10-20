@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

namespace TriWitnessAux

open TriangleInflation

variable {t : ℕ}

/-- The three diagonal outcomes, flattened into signs. -/
def flatD (t : ℕ) : (Fin t → ThreeBit) ≃ ((Σ _ : Fin t, Fin 3) → Bool) where
  toFun w := fun x => bitOf x.2 (w x.1)
  invFun u := fun l => (u ⟨l, 0⟩, u ⟨l, 1⟩, u ⟨l, 2⟩)
  left_inv w := by funext l; simp [bitOf]
  right_inv u := by
    funext x
    obtain ⟨l, g⟩ := x
    fin_cases g <;> rfl

end TriWitnessAux
end TriangleInflation.Graph
end
