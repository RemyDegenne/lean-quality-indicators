@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}}

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

variable [Quasicategory X]

/-- In a quasicategory, two left homotopic edges are also right homotopic. -/
noncomputable def HomotopyL.homotopyR {e e' : Edge x₀ x₁} (h : HomotopyL e e') :
    HomotopyR e e' :=
  assoc' (.idComp e) (.compId e) h

end Edge
end SSet
end
