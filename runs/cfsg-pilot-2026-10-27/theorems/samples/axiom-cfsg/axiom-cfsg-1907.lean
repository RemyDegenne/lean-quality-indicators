public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem apply_eq_zero_of_commute_diagU {n : ℕ} {d : Fin n → Kˣ} {g : GL (Fin n) K}
    (hg : g * diagU d = diagU d * g) {i j : Fin n} (hij : d i ≠ d j) :
    (g : Matrix (Fin n) (Fin n) K) i j = 0 :=
  CFSG.RankThree.PartOne.KFOUT3.apply_eq_zero_of_commute_diagU' hg hij

end CFSG.RankThree.PartOne.KFU
end
