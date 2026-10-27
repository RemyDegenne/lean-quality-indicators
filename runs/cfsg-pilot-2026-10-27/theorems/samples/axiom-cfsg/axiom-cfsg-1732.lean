public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux

open CFSG.Blueprint CFSG.AGLEmbedding

section B

theorem genData_B_three [Finite (NativeSporadic.Carrier .B)] [Fact (Nat.Prime 3)]
    (hc : 2 < Nat.card (NativeSporadic.Carrier .B)) : GenData (NativeSporadic.Carrier .B) 3 :=
  genData_of_tc_cp (X := NativeSporadic.B) (by norm_num)
    (CFSG.AGLEmbedding.BCox.tcGenDatum_B_three hc)
    (CFSG.AGLEmbedding.BCox.coverPointDatum_B_three hc)

end B
end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporAux
end
