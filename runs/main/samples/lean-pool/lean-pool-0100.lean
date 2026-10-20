@[expose] public section

noncomputable section

namespace Demazure

open MvPolynomial

variable {n : ℕ} (n_pos : n > 0)

lemma transposition_commutes_adjacent' {i : Fin n} (h0 : i < n + 1)
    (h1 : i + 1 < n + 1) (h2 : i + 2 < n + 1) :
    (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩ ∘
          (Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩) ∘
        (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩) :
      Fin (n + 1) → Fin (n + 1)) =
      Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩ ∘
        (Equiv.swap ⟨i, h0⟩ ⟨i + 1, h1⟩) ∘
          (Equiv.swap ⟨i + 1, h1⟩ ⟨i + 2, h2⟩) := by
  funext k
  exact transposition_commutes_adjacent h0 h1 h2

end Demazure
end
end
