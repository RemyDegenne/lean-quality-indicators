@[expose] public noncomputable section

open scoped MatrixOrder

open Filter

namespace ViscositySolns

variable {n : Nat}

@[simp]
theorem pointLeft_leftPointEmbedding (x : Point n) :
    pointLeft (n := n) (leftPointEmbedding (n := n) x) = x := by
  simp [pointLeft]

end ViscositySolns
end
