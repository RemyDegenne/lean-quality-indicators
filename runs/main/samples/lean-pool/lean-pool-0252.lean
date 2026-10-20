@[expose] public section

namespace LO

namespace FirstOrder

namespace Arith

scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n

namespace HierarchySymbol

variable (ξ : Type*) (n : ℕ)

variable {Γ : HierarchySymbol}

variable {ξ n}

namespace Semiformula

lemma sigma_prop : (φ : Sg-[m].Semiformula ξ n) → Hierarchy Sg m φ.val
  | mkSigma _ h => h

end Semiformula
end HierarchySymbol
end Arith
end FirstOrder
end LO
end
