public section

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ}

variable (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))

@[simp]
theorem relabel_relabel (σ' τ' : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).relabel σ' τ' = D.relabel (σ' * σ) (τ' * τ) := by
  rw [relabel_def, relabel_def, relabel_def, PerfectMatching.congr_trans,
    Equiv.Perm.sumCongr_trans]
  rfl

end BrauerDiagram
end TauCeti
end
