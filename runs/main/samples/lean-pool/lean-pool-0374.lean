@[expose] public section

namespace HermitianMat

variable {R n m α : Type*} [Star R] [TrivialStar R] [Fintype n] [Fintype m]

section RCLike

variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [RCLike 𝕜]

theorem trace_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) :
    (diagonal 𝕜 f).trace = ∑ i, f i := by
  rw [trace_eq_re_trace]
  simp [HermitianMat.diagonal, Matrix.trace]

end RCLike
end HermitianMat
end
