@[expose] public section

namespace QuantumAlg

open Matrix

open scoped ComplexOrder BigOperators

variable {r : ℕ}

/-- Off-diagonal Hermitian embedding of a feature vector `v` into `Fin 1 ⊕ Fin r`. -/
noncomputable def offDiagEmb (v : Fin r → ℂ) : Matrix (Fin 1 ⊕ Fin r) (Fin 1 ⊕ Fin r) ℂ :=
  Matrix.fromBlocks 0 (Matrix.of fun _ k => v k) (Matrix.of fun k _ => starRingEnd ℂ (v k)) 0

end QuantumAlg
end
