public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]

namespace burnsideF46_g2d_Data

variable {c : α.Completion Y} {Qx Ql : Subgroup c.G0} (D : burnsideF46_g2d_Data c Qx Ql)

include D

theorem trans_sphere {n : ℕ} (hn : n < 6) (a : c.Γ) {v w : c.Γ} (hv : c.graph.dist a v = n)
    (hw : c.graph.dist a w = n) : ∃ g : c.G0, g • a = a ∧ g • v = w := by
  cases ha : CosetGeom.vtype a
  · exact GPath.exists_fix_smul_eq_of_dist (m := 5) D.hval (D.transPt ha) (connected_graph c)
      (by omega) hv hw
  · exact GPath.exists_fix_smul_eq_of_dist (m := 4) D.hval (D.transLn ha) (connected_graph c)
      (by omega) hv hw

end burnsideF46_g2d_Data
end CFSG.ASVolI
end
