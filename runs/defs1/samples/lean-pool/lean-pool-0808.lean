@[expose] public section

namespace Matrix

variable {n 𝕜 : Type _} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix BigOperators ComplexOrder MatrixOrder

/-- Real powers of a Hermitian matrix, defined by spectral calculus. -/
noncomputable def _root_.Matrix.IsHermitian.rpow {Q : Matrix n n 𝕜}
    (hQ : IsHermitian Q) (r : ℝ) :
    Matrix n n 𝕜 :=
  Matrix.innerAut hQ.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ (hQ.eigenvalues ^ (r : ℝ) : n → ℝ) : n → 𝕜))

end Matrix
end
