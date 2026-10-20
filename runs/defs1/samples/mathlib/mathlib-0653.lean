@[expose] public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet

variable (X : SSet.{u})

namespace PtSimplex

variable {X} {n : ℕ} {x : X _⦋0⦌}

namespace MulStruct

section

variable [X.KanComplex] {p q r : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}

/-- A `MulStruct .const p q i` structure deduced from a `MulStruct p .const q i` structure. -/
@[no_expose]
noncomputable def oneMulEqOfMulOneEq (h : MulStruct p .const q i) :
    MulStruct .const p q i :=
  (assoc' (oneMul p i) h (mulOne p i)).oneMulEqSymm

end
end MulStruct
end PtSimplex
end SSet
end
