public section

open Set

namespace ENat

variable {ι : Sort*} {f : ι → ℕ} {s : Set ℕ}

variable {f : ι → ℕ∞} {s : Set ℕ∞}

variable {ι κ : Sort*} {f g : ι → ℕ∞} {s : Set ℕ∞} {a : ℕ∞}

lemma mul_sSup : a * sSup s = ⨆ b ∈ s, a * b := by
  simp_rw [sSup_eq_iSup, mul_iSup]

end ENat
end
