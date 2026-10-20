@[expose] public section

section SourceQuantumXorPolynomialMethod

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable {W : Type} [Fintype W] [DecidableEq W]

variable {O : Type} [DecidableEq O]

theorem exists_xor_probability_polynomial (A : QAlg ι Bool O W) (t : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb A.readout (xorState A a t) o :=
  (hasAmpPoly_xorState A t).exists_qProb_polynomial A.readout o

end QuantumQueryComplexity
end SourceQuantumXorPolynomialMethod
end
