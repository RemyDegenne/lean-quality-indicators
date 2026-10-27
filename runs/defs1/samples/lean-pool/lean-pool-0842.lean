@[expose] public section

namespace QuantumAlg

namespace WalshHadamard

open PureState Gate

noncomputable section

variable {n : ℕ}

/-- The `n`-qubit Hadamard layer as a unitary gate. -/
def hadamardLayer (n : ℕ) : Gate n :=
  Gate.ofUnitary (hadamardLayerOp n) (hadamardLayerOp_mem_unitaryGroup n)

end
end WalshHadamard
end QuantumAlg
end
