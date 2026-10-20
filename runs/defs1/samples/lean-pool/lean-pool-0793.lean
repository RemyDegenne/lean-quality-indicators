@[expose] public section

namespace QuantumAlg

open Kronecker

variable {m n : ℕ}

namespace HilbertOperator

section

/-- Tensor product of Hilbert-space operators. -/
noncomputable def tensor
    (G : HilbertOperator m) (K : HilbertOperator n) : HilbertOperator (m + n) :=
  Matrix.reindex prodEquiv prodEquiv (G ⊗ₖ K)

end
end HilbertOperator
end QuantumAlg
end
