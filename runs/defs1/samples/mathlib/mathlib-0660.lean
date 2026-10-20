@[expose] public section

universe u

open scoped Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable (P : A.Pairing)

section

variable {y : P.II} (hy : Acc P.AncestralRel y)

/-- Auxiliary definition for `SSet.Subcomplex.Pairing.Rank`. -/
noncomputable def rank' : ℕ :=
  Acc.recOn hy (fun y _ r ↦ ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)

end
end Pairing
end SSet.Subcomplex
end
