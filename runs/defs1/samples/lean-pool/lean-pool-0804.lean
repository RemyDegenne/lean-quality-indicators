@[expose] public section

namespace QECCertificates

open _root_.Matrix

open scoped BigOperators

variable {r₁ n₁ r₂ n₂ : ℕ}

/-- The preimage of right multiplication: `M *ᵥ preimage M y = y` whenever `y` lies in the column
span (see `preimage_spec`). -/
noncomputable def preimage {m k : ℕ} (M : Matrix (Fin m) (Fin k) (ZMod 2)) (y : Vec m) : Vec k :=
  if h : ∃ x : Vec k, M *ᵥ x = y then Classical.choose h else 0

end QECCertificates
end
