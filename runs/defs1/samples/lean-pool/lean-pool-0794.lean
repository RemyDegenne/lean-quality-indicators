@[expose] public section

namespace QuantumAlg

namespace QNNOverparametrization

variable (Q : QNNOverparametrization)

/-- The QNN is **overparametrized** at `M` parameters when the achievable Fisher
rank has saturated its dynamical-Lie-algebra bound. -/
def IsOverparametrized (M : ℕ) : Prop := Q.fisherRank M = Q.dlaDim

end QNNOverparametrization
end QuantumAlg
end
