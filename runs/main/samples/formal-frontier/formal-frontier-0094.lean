@[expose] public section

universe uR uD

attribute [instance] MatrixDivisionDecomposition.divisionRing
  MatrixDivisionDecomposition.blockSize_neZero

namespace MatrixDivisionDecomposition

variable (R : Type uR) [Ring R]

variable {R}

@[simp]
theorem ringEquiv_apply_symm_apply (p : MatrixDivisionDecomposition.{uR, uD} R)
    (a : ∀ i, Matrix (Fin (p.blockSize i)) (Fin (p.blockSize i)) (p.coefficient i)) :
    p.ringEquiv (p.ringEquiv.symm a) = a :=
  p.ringEquiv.apply_symm_apply a

end MatrixDivisionDecomposition
end
