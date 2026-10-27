@[expose] public section

namespace LO

namespace FirstOrder

variable {L : Language.{u}}

namespace Structure

variable (φ : L₁ →ᵥ L₂) {M : Type w} (s₂ : Structure L₂ M)

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Decidable (L : Language.{u}) (M : Type w) [s : Structure L M] :=
  {k : ℕ} → (r : L.Rel k) → (v : Fin k → M) → Decidable (s.rel r v)

end Structure
end FirstOrder
end LO
end
