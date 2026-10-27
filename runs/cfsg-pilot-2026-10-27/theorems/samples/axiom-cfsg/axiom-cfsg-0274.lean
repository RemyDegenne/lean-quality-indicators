public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Monster.Visible CFSG.Monster.SpinLattice

open scoped IsMulCommutative

theorem latOfRho_one : latOfRho (1 : rhoQvis) = 0 := by
  simp only [latOfRho, QuotientGroup.mk_one, ofMul_one]
  exact visModLat.map_zero

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
end
