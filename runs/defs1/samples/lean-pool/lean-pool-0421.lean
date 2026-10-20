@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Build a constant expression (always supported) -/
def mkConst (q : ℚ) : { e : Expr // ADSupported e } :=
  ⟨Expr.const q, ADSupported.const q⟩

end LeanCert.Engine
end
end
end
end
