@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The statement that `(x, y) ∈ C × D` is a local maximum point of
`(x', y') ↦ u x' - v y' - φ (x', y')` relative to `C × D`.
-/
def HasDoubledLocalMaximumOn (C D : Set (Point n)) (u v : Point n -> Real)
    (φ : DoubledPoint n -> Real) (x y : Point n) : Prop :=
  (x, y) ∈ C ×ˢ D ∧
    IsLocalMaxOn (fun q : DoubledPoint n => u q.1 - v q.2 - φ q) (C ×ˢ D) (x, y)

end ViscositySolns
end
