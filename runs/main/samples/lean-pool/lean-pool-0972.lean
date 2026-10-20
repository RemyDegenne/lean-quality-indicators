@[expose] public section

namespace RS

open Finset

variable {k ℓ : ℕ}

theorem blockSigmaEquiv_lt_of_block_lt :
    ∀ {ds : List ℕ} {v₁ v₂ : Fin ds.length}
      (_ : v₁ < v₂) (j₁ : Fin (ds.get v₁)) (j₂ : Fin (ds.get v₂)),
      blockSigmaEquiv ds ⟨v₁, j₁⟩ < blockSigmaEquiv ds ⟨v₂, j₂⟩
  | [], v₁, _, _, _, _ => v₁.elim0
  | d :: ds, v₁, v₂, hlt, j₁, j₂ => by
    match v₁, v₂ with
    | ⟨0, hv₁⟩, ⟨0, hv₂⟩ =>
      exact absurd hlt (lt_irrefl _)
    | ⟨0, hv₁⟩, ⟨w₂ + 1, hv₂⟩ =>
      rw [Fin.lt_def]
      have h1 : (blockSigmaEquiv (d :: ds) ⟨⟨0, hv₁⟩, j₁⟩).val =
          j₁.val := rfl
      have hw₂ : w₂ < ds.length := by
        simp only [List.length_cons] at hv₂; omega
      have h2 : (blockSigmaEquiv (d :: ds) ⟨⟨w₂ + 1, hv₂⟩, j₂⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨w₂, hw₂⟩, j₂⟩).val := rfl
      rw [h1, h2]
      have hj₁ : j₁.val < d := j₁.isLt
      omega
    | ⟨w₁ + 1, hv₁⟩, ⟨0, hv₂⟩ =>
      simp only [Fin.lt_def] at hlt
      omega
    | ⟨w₁ + 1, hv₁⟩, ⟨w₂ + 1, hv₂⟩ =>
      have hw₁ : w₁ < ds.length := by
        simp only [List.length_cons] at hv₁; omega
      have hw₂ : w₂ < ds.length := by
        simp only [List.length_cons] at hv₂; omega
      have hlt' : (⟨w₁, hw₁⟩ : Fin ds.length) < ⟨w₂, hw₂⟩ := by
        simp only [Fin.lt_def] at hlt ⊢; omega
      have hrec := blockSigmaEquiv_lt_of_block_lt hlt' j₁ j₂
      rw [Fin.lt_def]
      have h1 : (blockSigmaEquiv (d :: ds) ⟨⟨w₁ + 1, hv₁⟩, j₁⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨w₁, hw₁⟩, j₁⟩).val := rfl
      have h2 : (blockSigmaEquiv (d :: ds) ⟨⟨w₂ + 1, hv₂⟩, j₂⟩).val =
          d + (blockSigmaEquiv ds ⟨⟨w₂, hw₂⟩, j₂⟩).val := rfl
      rw [h1, h2]
      rw [Fin.lt_def] at hrec
      omega

end RS
end
