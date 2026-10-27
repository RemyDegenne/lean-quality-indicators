public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

open CFSG.Timmesfeld.RankOne CFSG.LieType.Universal Matrix

namespace Linear

section Swap

variable (F : Type*) [Field F] (N : ℕ)

theorem revMat_mul (M M' : Matrix (Fin N) (Fin N) F) :
    revMat F N (M * M') = revMat F N M' * revMat F N M := by
  rw [revMat, revMat, revMat, ← Matrix.submatrix_mul_equiv _ _ Fin.revPerm Fin.revPerm Fin.revPerm,
    Matrix.transpose_mul]

end Swap
end Linear
end CFSG.Timmesfeld.ARS
end
