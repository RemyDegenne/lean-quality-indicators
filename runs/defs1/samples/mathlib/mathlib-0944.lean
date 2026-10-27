@[expose] public section

open Finset

variable {𝕜 ι κ α β : Type*}

namespace Rel

section Asymmetric

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  (r : α → β → Prop) [∀ a, DecidablePred (r a)] {s s₁ s₂ : Finset α}
  {t t₁ t₂ : Finset β} {a : α} {b : β} {δ : 𝕜}

/-- Edge density of a relation between two finsets of vertices. -/
def edgeDensity (s : Finset α) (t : Finset β) : ℚ := #(interedges r s t) / (#s * #t)

end Asymmetric
end Rel
end
