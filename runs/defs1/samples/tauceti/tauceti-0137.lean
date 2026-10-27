public section

open scoped Nat

namespace TauCeti

/-- **Permutations are exactly the Brauer diagrams with no horizontal arc.** -/
noncomputable def permToBrauerEquiv (k : ℕ) :
    Equiv.Perm (Fin k) ≃ {D : BrauerDiagram k // ∀ x, D.IsThrough x} where
  toFun σ := ⟨permToBrauer σ, BrauerDiagram.isThrough_permToBrauer σ⟩
  invFun D := BrauerDiagram.throughPerm D.1 D.2
  left_inv σ := BrauerDiagram.throughPerm_permToBrauer σ
  right_inv D := Subtype.ext (BrauerDiagram.permToBrauer_throughPerm D.2)

end TauCeti
end
