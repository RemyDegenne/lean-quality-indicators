public section

namespace CFSG.StandardType.FF81.Blocks

open Matrix CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

open scoped MatrixGroups

theorem mk30_cases : ∀ a b c d : ZMod 2,
    mk30 a b c d * (mk30 a b c d).submatrix (Equiv.swap (0 : Fin 6) 3) (Equiv.swap (0 : Fin 6) 3) =
      (mk30 a b c d).submatrix (Equiv.swap (0 : Fin 6) 3) (Equiv.swap (0 : Fin 6) 3) * mk30 a b c d →
    mk30 a b c d * (mk30 a b c d).submatrix sw0345Perm sw0345Perm =
      (mk30 a b c d).submatrix sw0345Perm sw0345Perm * mk30 a b c d →
    mk30 a b c d = 1 ∨ mk30 a b c d = (tr6 3 4 : Matrix (Fin 6) (Fin 6) (ZMod 2)) ∨
      mk30 a b c d = (tr6 5 0 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  decide

end CFSG.StandardType.FF81.Blocks
end
