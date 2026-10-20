public section

namespace TauCeti

open Matrix

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

variable {m n : ℕ}

@[simp]
theorem jointEigenspaceMatrix_apply {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R)
    (a : Fin m → R) (i : Fin m) (j k : Fin n) :
    jointEigenspaceMatrix A a (finProdFinEquiv (i, j)) k =
      (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) j k := by
  simp [jointEigenspaceMatrix]

end TauCeti
end
