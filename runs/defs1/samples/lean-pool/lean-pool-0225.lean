public section

open CKN

noncomputable section

namespace CIV

variable {m : ℕ}

/-- The barrier `eq:aniso:comparison:barrier`:
`Ψ_σ(x, τ) = M + σ (⟨x⟩ + K (τ - τ₀))`. -/
@[expose] def barrier (m : ℕ) (M σ K τ₀ : ℝ) (z : Vec m × ℝ) : ℝ :=
  M + σ * (japaneseBracket m z.1 + K * (z.2 - τ₀))

end CIV
end
end
