public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv CFSG.Open CFSG.ClassicalInvolution.Solomon73

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

theorem cc_one (c : SC) : Y.cc 1 c = c := by
  apply Y.σA_injective
  rw [Y.σA_cc Y.NA.one_mem]
  group

end YData
end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
end
