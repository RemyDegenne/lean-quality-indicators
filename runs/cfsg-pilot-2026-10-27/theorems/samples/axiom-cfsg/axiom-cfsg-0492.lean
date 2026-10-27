public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

section Big

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem rho_apply (A : Matrix.SpecialLinearGroup (Fin 2) (Qext K)) (v : QV K (Fin 2)) :
    ((rhoL4 A : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v =
      Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) (Qext K)) v := by
  show Matrix.toLin' (A : Matrix (Fin 2) (Fin 2) (Qext K)) v = _
  rw [Matrix.toLin'_apply]

end Big
end CFSG.RankThree.PartOne.KFOUT3
end
