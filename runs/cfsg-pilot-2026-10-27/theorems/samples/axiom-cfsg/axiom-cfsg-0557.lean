public section

namespace CFSG.RankThree.GF2n.Smith81

theorem orthR0HypFour_of (hT : OrthTacitStatement) :
    OrthR0HypFourStatement := by
  intro G _ _ M Q Z B hc C h4 hTSP X x hs
  exact FourPlus.exists_mem_Lgen_of_data (FourPlus.Data.ofFrame hc (noA2_of_tacit hT hc) C h4 hTSP)
    hs

end CFSG.RankThree.GF2n.Smith81
end
