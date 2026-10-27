public section

open scoped Nat

namespace TauCeti

namespace BrauerDiagram

variable {k : ℕ} (D : BrauerDiagram k) (x : Fin k ⊕ Fin k)

/-- The boundary point `x` lies on a **cup**: it is a top point matched with another top
point. -/
def IsCup : Prop := x.isRight ∧ (D.val x).isRight

end BrauerDiagram
end TauCeti
end
