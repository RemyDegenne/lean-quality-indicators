@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace ComposableArrows

variable {n : ℕ} (S : ComposableArrows C n)

variable {S}

variable (S)

variable {S}

/-- Functoriality maps for `ComposableArrows.sc'`. -/
@[simps]
def sc'Map {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S₁.sc' h₁ i j k ⟶ S₂.sc' h₂ i j k where
  τ₁ := φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

end ComposableArrows
end CategoryTheory
end
