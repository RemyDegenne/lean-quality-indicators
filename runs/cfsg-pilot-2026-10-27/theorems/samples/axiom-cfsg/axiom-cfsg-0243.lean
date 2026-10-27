public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.SubgroupLists CFSG.Open

open scoped MatrixGroups

variable {K : Type} [Field K]

theorem dg_sq {g x : SL(3, K)} (hx : IsDiagIn g x) (hx2 : x ^ 2 = 1) (i : Fin 3) :
    dg g x i * dg g x i = 1 := by
  rw [← dg_mul hx hx, ← pow_two, hx2, dg_one]

end CFSG.Quasithin.E22S
end
