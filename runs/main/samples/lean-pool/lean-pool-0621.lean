@[expose] public section

namespace LO

namespace FirstOrder

namespace Arith

open LO.Arith

variable {ξ : Type*} {n : ℕ}

variable {V : Type*} [ORingStruc V]

variable {ℌ : HierarchySymbol} {Γ Γ' : SigmaPiDelta}

variable (ℌ)

variable {ℌ}

lemma _root_.LO.FirstOrder.Arith.BoldfaceBoundedFunction₁.definable {f : V → V} (h :
    BoldfaceBoundedFunction₁ f) :
    ℌ.BoldfaceFunction₁ f :=
  .of_zero h.2

end Arith
end FirstOrder
end LO
end
