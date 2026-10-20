@[expose] public section

namespace QuantumAlg

namespace Gate

noncomputable section

variable {n : ℕ}

@[simp]
theorem applyVec_add (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ + φ) = G.applyVec ψ + G.applyVec φ :=
  HilbertOperator.applyVec_add (G : HilbertOperator n) ψ φ

end
end Gate
end QuantumAlg
end
